;;;; symbolic-ai.lisp - a small symbolic AI in Common Lisp (SBCL), in one file.
;;;;
;;;; USAGE (from the repository root; SAI_MODE picks what runs, default demo)
;;;;   sbcl --noinform --non-interactive --load symbolic-ai.lisp                 demo
;;;;   SAI_MODE=validate sbcl --noinform --non-interactive --load symbolic-ai.lisp
;;;;   SAI_MODE=evolve   sbcl --noinform --non-interactive --load symbolic-ai.lisp
;;;;   (record-failure is used only by the workflow)
;;;;
;;;; MODEL
;;;;   Fact     a list like (parent alice bob). No variables, no strings.
;;;;   Variable a symbol starting with ?, like ?x.
;;;;   Rule     (rule name (if cond1 cond2 ...) (then conclusion))
;;;;   Built-in (different ?a ?b), holds when both are bound and unequal.
;;;;            Put it last in a rule, after the variables are bound.
;;;;
;;;; AUTOMATION (see .github/workflows/autoevolve.yml)
;;;;   Each run applies ONE lesson from *LESSONS* below (at most 10 plain facts or
;;;;   rules, never executed as code), appends it to knowledge/learned.lisp,
;;;;   validates, and writes PROGRESS.md and progress/*. On failure it rolls back
;;;;   and records why. It never writes outside: knowledge/learned.lisp,
;;;;   PROGRESS.md, progress/*. Lessons live in this file, so adding lessons means
;;;;   editing this file on your main branch.
;;;;
;;;; ROADMAP (small steps, tests and Python/neural parts deferred by choice)
;;;;   1 Engine: index facts by predicate; numeric built-ins; negation as failure
;;;;     (stratified); retraction with dependent facts.
;;;;   2 Explanations: "why not?" (which condition failed); proof trees as data;
;;;;     plain-English templates; contradiction detection.
;;;;   3 Queries: conjunctive queries; backward chaining with unification; a REPL.
;;;;   4 Knowledge management: modules; provenance (source, date, confidence);
;;;;     export/import of s-expressions.
;;;;   5 Language: controlled English in ("Alice is a parent of Bob"), templates out.
;;;;   6 Planning: STRIPS-style planner; simple constraint solving.
;;;;   7 Later: a narrow bridge to neural components that only PROPOSE facts or
;;;;     rules, going through the same validation and review path as lessons.

(defpackage :symbolic-ai
  (:use :cl))

(in-package :symbolic-ai)

;;; ======================================================================
;;; Paths and printing
;;; ======================================================================

(defparameter *root*
  (make-pathname :name nil :type nil :version nil :defaults *load-truename*))

(defun project-path (relative)
  (merge-pathnames relative *root*))

(defun show (object)
  "One line, lower-case, no package prefixes."
  (let ((*package* (find-package :symbolic-ai))
        (*print-pretty* nil))
    (string-downcase (prin1-to-string object))))

;;; ======================================================================
;;; Knowledge base
;;; ======================================================================

(defstruct (rule (:constructor make-rule (name conditions conclusion)))
  name conditions conclusion)

(defstruct kb
  (facts '())                                  ; insertion order
  (rules '())
  (why (make-hash-table :test 'equal)))        ; fact -> (:given) or (:derived rule supports)

(defun variable-p (x)
  (and (symbolp x)
       (plusp (length (symbol-name x)))
       (char= (char (symbol-name x) 0) #\?)))

(defun ground-p (form)
  (cond ((variable-p form) nil)
        ((consp form) (and (ground-p (car form)) (ground-p (cdr form))))
        (t t)))

(defun variables-in (form)
  (cond ((variable-p form) (list form))
        ((consp form) (union (variables-in (car form)) (variables-in (cdr form))))
        (t '())))

(defun builtin-condition-p (condition)
  (and (consp condition) (eq (first condition) 'different)))

(defun builtin-holds-p (condition)
  (destructuring-bind (op a b) condition
    (declare (ignore op))
    (and (ground-p a) (ground-p b) (not (equal a b)))))

(defun match-variable (var datum bindings)
  (let ((binding (assoc var bindings)))
    (cond ((null binding) (acons var datum bindings))
          ((equal (cdr binding) datum) bindings)
          (t :fail))))

(defun match (pattern datum &optional (bindings '()))
  "Bindings alist on success, :FAIL otherwise."
  (cond ((eq bindings :fail) :fail)
        ((variable-p pattern) (match-variable pattern datum bindings))
        ((atom pattern) (if (equal pattern datum) bindings :fail))
        ((consp datum)
         (match (cdr pattern) (cdr datum)
                (match (car pattern) (car datum) bindings)))
        (t :fail)))

(defun substitute-bindings (form bindings)
  (cond ((variable-p form)
         (let ((binding (assoc form bindings)))
           (if binding (cdr binding) form)))
        ((consp form)
         (cons (substitute-bindings (car form) bindings)
               (substitute-bindings (cdr form) bindings)))
        (t form)))

(defun known-p (kb fact)
  (and (gethash fact (kb-why kb)) t))

(defun add-fact (kb fact &optional (justification (list :given)))
  "Returns T if FACT was new."
  (unless (and (consp fact) (ground-p fact))
    (error "A fact must be a list without variables: ~a" (show fact)))
  (cond ((known-p kb fact) nil)
        (t (setf (kb-facts kb) (append (kb-facts kb) (list fact))
                 (gethash fact (kb-why kb)) justification)
           t)))

(defun add-rule (kb rule)
  (when (find (rule-name rule) (kb-rules kb) :key #'rule-name)
    (error "Duplicate rule name: ~a" (rule-name rule)))
  (let ((unbound (set-difference
                  (variables-in (rule-conclusion rule))
                  (variables-in (remove-if #'builtin-condition-p
                                           (rule-conditions rule))))))
    (when unbound
      (error "Rule ~a: conclusion uses variables its conditions never bind: ~a"
             (rule-name rule) (show unbound))))
  (setf (kb-rules kb) (append (kb-rules kb) (list rule)))
  rule)

(defun parse-rule (form)
  (destructuring-bind (tag name if-clause then-clause) form
    (unless (and (eq tag 'rule)
                 (symbolp name)
                 (consp if-clause) (eq (first if-clause) 'if) (rest if-clause)
                 (every (lambda (c)
                          (and (consp c)
                               (or (not (builtin-condition-p c)) (= (length c) 3))))
                        (rest if-clause))
                 (consp then-clause) (eq (first then-clause) 'then)
                 (= (length then-clause) 2))
      (error "Malformed rule: ~a" (show form)))
    (make-rule name (rest if-clause) (second then-clause))))

(defun apply-knowledge-form (kb form)
  (unless (consp form)
    (error "Not a knowledge form: ~a" (show form)))
  (case (first form)
    (fact (add-fact kb (second form)))
    (rule (add-rule kb (parse-rule form)))
    (t (error "Unknown knowledge form: ~a" (show form)))))

(defun read-forms (path)
  "Read all forms from PATH with reader code execution disabled."
  (with-open-file (in path :direction :input)
    (let ((*package* (find-package :symbolic-ai))
          (*read-eval* nil))
      (loop for form = (read in nil in)
            until (eq form in)
            collect form))))

;;; ======================================================================
;;; Inference and explanation
;;; ======================================================================

(defparameter *max-rounds* 50)
(defparameter *max-facts* 5000)

(defun satisfy (kb conditions bindings support)
  "All ways to satisfy CONDITIONS: a list of (bindings . supporting-facts)."
  (if (null conditions)
      (list (cons bindings (reverse support)))
      (let ((pattern (substitute-bindings (first conditions) bindings)))
        (if (builtin-condition-p pattern)
            (if (builtin-holds-p pattern)
                (satisfy kb (rest conditions) bindings support)
                '())
            (let ((results '()))
              (dolist (fact (kb-facts kb))
                (let ((b (match pattern fact bindings)))
                  (unless (eq b :fail)
                    (dolist (r (satisfy kb (rest conditions) b (cons fact support)))
                      (push r results)))))
              (nreverse results))))))

(defun forward-chain (kb &key (max-rounds *max-rounds*) (max-facts *max-facts*))
  "Apply rules until nothing new appears or a limit is hit.
Returns (values new-facts reason): :fixpoint, :round-limit or :fact-limit."
  (let ((derived '()))
    (dotimes (round max-rounds)
      (declare (ignorable round))
      (let ((changed nil))
        (dolist (rule (kb-rules kb))
          (dolist (found (satisfy kb (rule-conditions rule) '() '()))
            (let ((fact (substitute-bindings (rule-conclusion rule) (car found))))
              (when (add-fact kb fact (list :derived (rule-name rule) (cdr found)))
                (push fact derived)
                (setf changed t)
                (when (>= (length (kb-facts kb)) max-facts)
                  (return-from forward-chain
                    (values (nreverse derived) :fact-limit)))))))
        (unless changed
          (return-from forward-chain (values (nreverse derived) :fixpoint)))))
    (values (nreverse derived) :round-limit)))

(defun query (kb pattern)
  "A list of binding alists, one per known fact matching PATTERN."
  (let ((results '()))
    (dolist (fact (kb-facts kb) (nreverse results))
      (let ((b (match pattern fact '())))
        (unless (eq b :fail)
          (push (reverse b) results))))))

(defun explain (kb fact &key (stream *standard-output*) (depth 0))
  "Print whether FACT is given, or which rule and facts derived it."
  (let ((why (gethash fact (kb-why kb)))
        (pad (make-string (* 2 depth) :initial-element #\Space)))
    (cond ((null why)
           (format stream "~a~a -- not known~%" pad (show fact)))
          ((eq (first why) :given)
           (format stream "~a~a -- given~%" pad (show fact)))
          (t
           (format stream "~a~a -- derived by rule ~(~a~)~%"
                   pad (show fact) (second why))
           (dolist (support (third why))
             (explain kb support :stream stream :depth (1+ depth)))))))

;;; ======================================================================
;;; Starting knowledge (hand-written; the automation never edits this)
;;; ======================================================================

(defparameter *base-knowledge*
  '((fact (parent alice bob))
    (fact (parent bob carol))
    (fact (parent carol dave))
    (fact (parent alice erin))
    (fact (human socrates))

    (rule parent-is-ancestor
      (if (parent ?x ?y))
      (then (ancestor ?x ?y)))

    (rule ancestor-extends
      (if (parent ?x ?y) (ancestor ?y ?z))
      (then (ancestor ?x ?z)))

    (rule grandparent-rule
      (if (parent ?x ?y) (parent ?y ?z))
      (then (grandparent ?x ?z)))

    (rule humans-are-mortal
      (if (human ?x))
      (then (mortal ?x)))))

(defparameter *learned-header*
  (format nil ";;;; Appended to by the automation, one lesson per run.~%;;;; Review changes on the autoevolve branch before merging.~%"))

(defun make-project-kb ()
  "Base knowledge plus whatever the automation has learned so far."
  (let ((kb (make-kb))
        (learned (project-path "knowledge/learned.lisp")))
    (dolist (form *base-knowledge*)
      (apply-knowledge-form kb form))
    (when (probe-file learned)
      (dolist (form (read-forms learned))
        (apply-knowledge-form kb form)))
    kb))

;;; ======================================================================
;;; Lessons: the queue the automation draws from, one per run, in order.
;;; Data only: up to 10 plain (fact ...) or (rule ...) forms of symbols/numbers.
;;; Keep ids unique, rule names unique, and :title/:why on one line.
;;; ======================================================================

(defparameter *lessons*
  '((:id "L001" :title "Sibling relation"
     :why "Two different people with the same parent are siblings; uses the built-in DIFFERENT test."
     :forms ((rule sibling-rule
               (if (parent ?p ?a) (parent ?p ?b) (different ?a ?b))
               (then (sibling ?a ?b)))))

    (:id "L002" :title "Grandchild relation"
     :why "The inverse of grandparent."
     :forms ((rule grandchild-rule
               (if (grandparent ?x ?y))
               (then (grandchild ?y ?x)))))

    (:id "L003" :title "Aunt or uncle (pibling)"
     :why "A sibling of someone's parent. Depends on the sibling rule from L001."
     :forms ((rule pibling-rule
               (if (sibling ?s ?p) (parent ?p ?c))
               (then (pibling ?s ?c)))))

    (:id "L004" :title "Small animal taxonomy"
     :why "Adds is-a facts and makes is-a transitive."
     :forms ((fact (is-a dog mammal))
             (fact (is-a cat mammal))
             (fact (is-a mammal animal))
             (fact (is-a sparrow bird))
             (fact (is-a bird animal))
             (rule is-a-transitive
               (if (is-a ?x ?y) (is-a ?y ?z))
               (then (is-a ?x ?z)))))

    (:id "L005" :title "Property inheritance"
     :why "Things inherit properties from the categories they belong to."
     :forms ((fact (has animal cells))
             (fact (has mammal fur))
             (fact (has bird feathers))
             (rule inherit-property
               (if (is-a ?x ?y) (has ?y ?p))
               (then (has ?x ?p)))))

    (:id "L006" :title "Cousin relation"
     :why "Children of two siblings are cousins."
     :forms ((rule cousin-rule
               (if (parent ?p1 ?a) (parent ?p2 ?b) (sibling ?p1 ?p2))
               (then (cousin ?a ?b)))))))

;;; ======================================================================
;;; Validation
;;; ======================================================================

(defun validate-project ()
  "Check that knowledge loads, inference terminates, and every fact can be
explained. Returns (values ok-p problems stats)."
  (let ((problems '())
        (stats nil))
    (handler-case
        (let* ((kb (make-project-kb))
               (given (length (kb-facts kb))))
          (multiple-value-bind (derived reason) (forward-chain kb)
            (declare (ignore derived))
            (unless (eq reason :fixpoint)
              (push (format nil "inference stopped early: ~(~a~)" reason) problems)))
          (dolist (fact (kb-facts kb))
            (explain kb fact :stream (make-broadcast-stream)))
          (setf stats (list :rules (length (kb-rules kb))
                            :given given
                            :total (length (kb-facts kb)))))
      (error (e)
        (push (format nil "~a" e) problems)))
    (values (null problems) (reverse problems) stats)))

(defun run-validate ()
  "Exit code 0 = OK, 1 = failed. A smoke check, not a test suite."
  (multiple-value-bind (ok problems stats) (validate-project)
    (cond (ok
           (format t "OK: ~d rules, ~d given facts, ~d facts after inference.~%"
                   (getf stats :rules) (getf stats :given) (getf stats :total))
           (sb-ext:exit :code 0))
          (t
           (format t "VALIDATION FAILED:~%~{  - ~a~%~}" problems)
           (sb-ext:exit :code 1)))))

;;; ======================================================================
;;; Demo
;;; ======================================================================

(defparameter *demo-questions*
  '((grandparent alice ?who)
    (ancestor ?who dave)
    (mortal socrates)
    (sibling bob ?who)))   ; no answers until lesson L001 has been applied

(defun print-answers (kb pattern)
  (let ((answers (query kb pattern)))
    (format t "Q: ~a~%" (show pattern))
    (if (null answers)
        (format t "  no answers~%")
        (dolist (bindings answers)
          (when bindings
            (format t "  ~{~a~^, ~}~%"
                    (mapcar (lambda (pair)
                              (format nil "~a = ~a" (show (car pair)) (show (cdr pair))))
                            bindings)))
          (explain kb (substitute-bindings pattern bindings) :depth 1)))
    (terpri)))

(defun run-demo ()
  (let ((kb (make-project-kb)))
    (format t "Loaded ~d facts and ~d rules.~%"
            (length (kb-facts kb)) (length (kb-rules kb)))
    (multiple-value-bind (derived reason) (forward-chain kb)
      (format t "Inference stopped: ~(~a~). ~d new facts derived.~%~%"
              reason (length derived)))
    (dolist (pattern *demo-questions*)
      (print-answers kb pattern))
    (values)))

;;; ======================================================================
;;; Evolution: one bounded step per run
;;; Writes only: knowledge/learned.lisp, PROGRESS.md, progress/*
;;; Runs no shell commands and never evaluates lesson contents as code.
;;; ======================================================================

(defparameter *max-forms-per-lesson* 10)
(defparameter *max-log-entries* 30)

(defun utc-fields ()
  "(year month day hour minute) in UTC."
  (multiple-value-bind (sec minute hour day month year)
      (decode-universal-time (get-universal-time) 0)
    (declare (ignore sec))
    (list year month day hour minute)))

(defun utc-date ()
  (destructuring-bind (y mo d h mi) (utc-fields)
    (declare (ignore h mi))
    (format nil "~4,'0d-~2,'0d-~2,'0d" y mo d)))

(defun utc-stamp ()
  (destructuring-bind (y mo d h mi) (utc-fields)
    (format nil "~4,'0d-~2,'0d-~2,'0d ~2,'0d:~2,'0d UTC" y mo d h mi)))

(defun file-string (path)
  (with-open-file (in path :direction :input)
    (let* ((buffer (make-string (file-length in)))
           (count (read-sequence buffer in)))
      (subseq buffer 0 count))))

(defun write-text (path text &key append)
  (ensure-directories-exist path)
  (with-open-file (out path :direction :output
                            :if-exists (if append :append :supersede)
                            :if-does-not-exist :create)
    (write-string text out)))

(defun one-line (string)
  (substitute #\Space #\Return (substitute #\Space #\Newline string)))

(defun plain-data-p (x)
  "Only conses, integers, and symbols from this package or CL."
  (cond ((consp x) (and (plain-data-p (car x)) (plain-data-p (cdr x))))
        ((symbolp x) (and (member (symbol-package x)
                                  (list (find-package :symbolic-ai) (find-package :cl)))
                          t))
        (t (integerp x))))

(defun ensure-learned-file ()
  (let ((path (project-path "knowledge/learned.lisp")))
    (unless (probe-file path)
      (write-text path *learned-header*))))

(defun read-state ()
  (let ((path (project-path "progress/state.lisp")))
    (if (probe-file path)
        (let ((form (first (read-forms path))))
          (list :applied (getf form :applied)
                :failed (getf form :failed)
                :runs (or (getf form :runs) 0)
                :log (getf form :log)))
        (list :applied nil :failed nil :runs 0 :log nil))))

(defun write-state (state)
  (write-text
   (project-path "progress/state.lisp")
   (with-output-to-string (s)
     (let ((*package* (find-package :symbolic-ai))
           (*print-pretty* t)
           (*print-right-margin* 100))
       (format s ";;;; Written by the automation. Delete this file to reset progress.~%")
       (prin1 state s)
       (terpri s)))))

(defun next-lesson (lessons state)
  (find-if (lambda (lesson)
             (let ((id (getf lesson :id)))
               (not (or (member id (getf state :applied) :test #'equal)
                        (member id (getf state :failed) :test #'equal)))))
           lessons))

(defun check-lesson (lesson)
  (let ((id (getf lesson :id))
        (forms (getf lesson :forms)))
    (unless (and (stringp id) (stringp (getf lesson :title)) (stringp (getf lesson :why)))
      (error "A lesson needs string :id, :title and :why"))
    (unless (and (consp forms) (<= (length forms) *max-forms-per-lesson*))
      (error "Lesson ~a must have between 1 and ~d forms" id *max-forms-per-lesson*))
    (dolist (form forms)
      (unless (and (consp form)
                   (member (first form) '(fact rule))
                   (plain-data-p form))
        (error "Lesson ~a has a form that is not a plain fact or rule: ~a"
               id (show form))))
    t))

(defun lesson-block (lesson)
  (with-output-to-string (s)
    (format s "~%;; --- ~a: ~a (applied ~a) ---~%;; ~a~%"
            (one-line (getf lesson :id))
            (one-line (getf lesson :title))
            (utc-stamp)
            (one-line (getf lesson :why)))
    (dolist (form (getf lesson :forms))
      (format s "~a~%" (show form)))))

(defun apply-lesson (lesson)
  "Append LESSON to knowledge/learned.lisp and validate; roll back on any problem.
Returns (values applied-p note stats)."
  (let* ((path (project-path "knowledge/learned.lisp"))
         (original (if (probe-file path) (file-string path) *learned-header*)))
    (handler-case
        (progn
          (check-lesson lesson)
          ;; Dry run on a scratch KB: catches malformed forms and duplicate names.
          (let ((scratch (make-project-kb)))
            (dolist (form (getf lesson :forms))
              (apply-knowledge-form scratch form)))
          (write-text path (concatenate 'string original (lesson-block lesson)))
          (multiple-value-bind (ok problems stats) (validate-project)
            (cond (ok
                   (values t
                           "Validated: the knowledge base loaded in SBCL and inference reached a fixpoint."
                           stats))
                  (t
                   (write-text path original)
                   (values nil
                           (format nil "Validation failed; change rolled back: ~{~a~^; ~}" problems)
                           nil)))))
      (error (e)
        (write-text path original)
        (values nil (format nil "Rejected; change rolled back: ~a" e) nil)))))

(defun status-label (status)
  (ecase status
    (:applied "Applied a lesson")
    (:failed "Lesson failed validation (change discarded)")
    (:noop "No useful improvement available")
    (:blocked "Stopped: the project did not validate before any change")))

(defun render-run (entry)
  (with-output-to-string (s)
    (format s "### ~a - ~a~%~%" (getf entry :time) (status-label (getf entry :status)))
    (when (getf entry :lesson)
      (format s "- Lesson: ~a - ~a~%" (getf entry :lesson) (getf entry :title)))
    (format s "- Result: ~a~%" (getf entry :note))
    (let ((stats (getf entry :stats)))
      (when stats
        (format s "- Knowledge now: ~d rules, ~d given facts, ~d facts after inference~%"
                (getf stats :rules) (getf stats :given) (getf stats :total))))
    (terpri s)))

(defun describe-rule (rule)
  (format nil "if ~{~a~^ and ~} then ~a"
          (mapcar #'show (rule-conditions rule))
          (show (rule-conclusion rule))))

(defun render-progress (state)
  (let* ((kb (ignore-errors (make-project-kb)))
         (history (getf state :log))
         (latest (first history))
         (applied (getf state :applied))
         (failed (getf state :failed))
         (upcoming (next-lesson *lessons* state))
         (stats (nth-value 2 (validate-project))))
    (with-output-to-string (s)
      (format s "# Progress~%~%")
      (format s "_Generated by symbolic-ai.lisp on every run. Do not edit by hand._~%~%")
      (format s "## Status~%~%")
      (if latest
          (format s "- Last run: ~a - ~a~%" (getf latest :time) (status-label (getf latest :status)))
          (format s "- Last run: none yet~%"))
      (format s "- Runs so far: ~d~%" (getf state :runs))
      (format s "- Lessons applied: ~d of ~d~%" (length applied) (length *lessons*))
      (when failed
        (format s "- Lessons that failed and were skipped: ~{~a~^, ~}~%" failed))
      (when stats
        (format s "- Knowledge now: ~d rules, ~d given facts, ~d facts after inference~%"
                (getf stats :rules) (getf stats :given) (getf stats :total)))
      (format s "- Next lesson: ~a~%"
              (if upcoming
                  (format nil "~a - ~a" (getf upcoming :id) (getf upcoming :title))
                  "none (queue exhausted; add lessons to *lessons* in symbolic-ai.lisp)"))
      (format s "~%## Rules the assistant knows~%~%")
      (if kb
          (dolist (rule (kb-rules kb))
            (format s "- ~(~a~): ~a~%" (rule-name rule) (describe-rule rule)))
          (format s "- unavailable: the knowledge base failed to load~%"))
      (format s "~%## Lessons applied~%~%")
      (if applied
          (dolist (lesson *lessons*)
            (when (member (getf lesson :id) applied :test #'equal)
              (format s "- ~a - ~a: ~a~%"
                      (getf lesson :id) (getf lesson :title) (getf lesson :why))))
          (format s "- none yet~%"))
      (format s "~%## Recent runs (newest first)~%~%")
      (if history
          (dolist (entry (subseq history 0 (min 10 (length history))))
            (format s "- ~a - ~a~@[ (~a)~]~%"
                    (getf entry :time) (status-label (getf entry :status)) (getf entry :lesson)))
          (format s "- none yet~%"))
      (format s "~%## How to read this~%~%")
      (format s "- Detailed history: progress/ (one file per UTC day).~%")
      (format s "- New knowledge appears in knowledge/learned.lisp on the autoevolve branch.~%")
      (format s "- Nothing is merged into your main branch until you merge it.~%"))))

(defun finish (state status lesson note stats)
  (let* ((id (and lesson (getf lesson :id)))
         (entry (list :time (utc-stamp) :status status :lesson id
                      :title (and lesson (getf lesson :title))
                      :note note :stats stats))
         (history (cons entry (getf state :log)))
         (new-state
           (list :applied (if (and id (eq status :applied))
                              (append (getf state :applied) (list id))
                              (getf state :applied))
                 :failed (if (and id (eq status :failed))
                             (append (getf state :failed) (list id))
                             (getf state :failed))
                 :runs (1+ (getf state :runs))
                 :log (if (> (length history) *max-log-entries*)
                          (subseq history 0 *max-log-entries*)
                          history)))
         (date (utc-date))
         (dated (project-path (format nil "progress/~a.md" date))))
    (write-state new-state)
    (write-text dated
                (concatenate 'string
                             (if (probe-file dated) "" (format nil "# Progress for ~a~%~%" date))
                             (render-run entry))
                :append t)
    (write-text (project-path "progress/latest.md")
                (format nil "# Latest automation run~%~%~a" (render-run entry)))
    (write-text (project-path "progress/latest-status.txt")
                (format nil "~(~a~)~%" status))
    (write-text (project-path "PROGRESS.md") (render-progress new-state))
    (format t "status: ~(~a~)~%~a~%" status note)
    status))

(defun evolve-step (record-failure-p)
  "Apply one lesson, or (when RECORD-FAILURE-P) mark the next lesson failed
without applying it. The workflow uses that after its fresh-process check fails."
  (ensure-learned-file)
  (let* ((state (read-state))
         (lesson (next-lesson *lessons* state)))
    (if record-failure-p
        (finish state :failed lesson
                "Validation in a fresh SBCL process failed after the change; the workflow discarded it."
                nil)
        (multiple-value-bind (ok problems stats) (validate-project)
          (cond ((not ok)
                 (finish state :blocked nil
                         (format nil "The project does not validate before any change (~{~a~^; ~}). Nothing was changed."
                                 problems)
                         nil))
                ((null lesson)
                 (finish state :noop nil
                         "Every lesson has been applied or skipped. Add lessons to *lessons* in symbolic-ai.lisp."
                         stats))
                (t
                 (multiple-value-bind (applied note new-stats) (apply-lesson lesson)
                   (finish state (if applied :applied :failed) lesson note new-stats))))))))

;;; ======================================================================
;;; Entry point
;;; ======================================================================

(defun main ()
  (let ((mode (or (sb-ext:posix-getenv "SAI_MODE") "demo")))
    (cond ((string= mode "demo") (run-demo))
          ((string= mode "validate") (run-validate))
          ((string= mode "evolve") (evolve-step nil))
          ((string= mode "record-failure") (evolve-step t))
          (t (error "Unknown SAI_MODE: ~a" mode)))))

(main)
