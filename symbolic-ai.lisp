;;;; symbolic-ai.lisp - a small symbolic AI in Common Lisp (SBCL), in one file.
;;;;
;;;; USAGE (from the repository root; SAI_MODE picks what runs, default demo)
;;;;   sbcl --noinform --non-interactive --load symbolic-ai.lisp                 demo
;;;;   SAI_MODE=validate sbcl --noinform --non-interactive --load symbolic-ai.lisp
;;;;   SAI_MODE=evolve   sbcl --noinform --non-interactive --load symbolic-ai.lisp
;;;;   SAI_MODE=facts    ...            print every fact after inference
;;;;                                    (SAI_PREDICATES=suggest,alert limits it)
;;;;   SAI_MODE=load     ...            just load, e.g. to explore in a REPL
;;;;   (record-failure is used only by the workflow)
;;;;
;;;; MODEL
;;;;   Fact     a list like (parent alice bob). No variables, no strings.
;;;;   Variable a symbol starting with ?, like ?x.
;;;;   Rule     (rule name (if cond1 cond2 ...) (then conclusion))
;;;;   Built-ins, used as rule conditions. Their variables must already be bound
;;;;   by an earlier condition, so put them after the conditions that bind them:
;;;;     (different ?a ?b)       holds when the two values differ
;;;;     (lt|gt|le|ge ?a ?b)     integer comparison
;;;;     (add|sub|mul ?a ?b ?c)  integer arithmetic; ?c is bound to the result
;;;;     (not (pattern ...))     holds when no such fact is known (negation as
;;;;                             failure). Rules using NOT run in a second phase,
;;;;                             after all other rules have settled; if a later
;;;;                             fact contradicts a NOT assumption, inference
;;;;                             reports :negation-conflict instead of hiding it.
;;;;   Retraction: (retract-fact kb fact) removes a given fact and everything
;;;;   that depended on it, and returns the facts that disappeared.
;;;;
;;;; AUTOMATION (see .github/workflows/autoevolve.yml)
;;;;   Each run applies ONE lesson from *LESSONS* below (at most 10 plain facts or
;;;;   rules, never executed as code), appends it to knowledge/learned.lisp,
;;;;   validates, and writes PROGRESS.md and progress/*. On failure it rolls back
;;;;   and records why. It never writes outside: knowledge/learned.lisp,
;;;;   PROGRESS.md, progress/*. Lessons live in this file, so adding lessons means
;;;;   editing this file on your main branch.
;;;;
;;;; DIRECTION
;;;;   Loosely modelled on a JARVIS-style assistant: it knows about rooms and
;;;;   devices, system status, schedules, people and permissions, makes
;;;;   suggestions, and can always explain why. Lessons are ordered so those
;;;;   assistant skills arrive early (L010 onward).
;;;;
;;;; ROADMAP (small steps, tests and Python/neural parts deferred by choice)
;;;;   1 Engine (DONE): fact index by predicate; integer built-ins; negation as
;;;;     failure (two phases plus a conflict check, not full stratification);
;;;;     retraction with dependent facts.
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
  (why (make-hash-table :test 'equal))         ; fact -> (:given) or (:derived rule supports)
  (index (make-hash-table :test 'eql)))        ; predicate symbol -> its facts, insertion order

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

;;; Built-in conditions and how many parts each has, including its name.
(defparameter *builtin-arity*
  '((different . 3) (lt . 3) (gt . 3) (le . 3) (ge . 3)
    (add . 4) (sub . 4) (mul . 4) (not . 2)))

(defun builtin-condition-p (condition)
  (and (consp condition)
       (symbolp (first condition))
       (assoc (first condition) *builtin-arity*)
       t))

(defun condition-ok-p (condition)
  "A condition is a list; built-ins must have the right number of parts."
  (and (consp condition)
       (or (not (builtin-condition-p condition))
           (and (= (length condition)
                   (cdr (assoc (first condition) *builtin-arity*)))
                (or (not (eq (first condition) 'not))
                    (consp (second condition)))))))

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
  (when (eq (first fact) 'not)
    (error "A fact cannot start with NOT: ~a" (show fact)))
  (cond ((known-p kb fact) nil)
        (t (setf (kb-facts kb) (append (kb-facts kb) (list fact))
                 (gethash fact (kb-why kb)) justification)
           (when (symbolp (first fact))
             (setf (gethash (first fact) (kb-index kb))
                   (append (gethash (first fact) (kb-index kb)) (list fact))))
           t)))

(defun check-rule-bindings (rule)
  "Signal an error if a built-in uses a variable no earlier condition binds, or
if the conclusion uses a variable nothing binds."
  (let ((bound '()))
    (dolist (condition (rule-conditions rule))
      (if (builtin-condition-p condition)
          (let* ((arithmetic (member (first condition) '(add sub mul)))
                 (inputs (if arithmetic
                             (list (second condition) (third condition))
                             (rest condition)))
                 (outputs (if arithmetic (list (fourth condition)) '()))
                 (missing (set-difference (variables-in inputs) bound)))
            (when missing
              (error "Rule ~a: ~a uses variables no earlier condition binds: ~a"
                     (rule-name rule) (show condition) (show missing)))
            (setf bound (union bound (variables-in outputs))))
          (setf bound (union bound (variables-in condition)))))
    (let ((unbound (set-difference (variables-in (rule-conclusion rule)) bound)))
      (when unbound
        (error "Rule ~a: conclusion uses variables its conditions never bind: ~a"
               (rule-name rule) (show unbound))))))

(defun add-rule (kb rule)
  (when (find (rule-name rule) (kb-rules kb) :key #'rule-name)
    (error "Duplicate rule name: ~a" (rule-name rule)))
  (check-rule-bindings rule)
  (setf (kb-rules kb) (append (kb-rules kb) (list rule)))
  rule)

(defun parse-rule (form)
  (destructuring-bind (tag name if-clause then-clause) form
    (unless (and (eq tag 'rule)
                 (symbolp name)
                 (consp if-clause) (eq (first if-clause) 'if) (rest if-clause)
                 (every #'condition-ok-p (rest if-clause))
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

(defun candidate-facts (kb pattern)
  "Facts that could match PATTERN: those of its predicate when that is a plain
symbol, otherwise every fact."
  (if (and (consp pattern)
           (symbolp (first pattern))
           (not (variable-p (first pattern))))
      (gethash (first pattern) (kb-index kb))
      (kb-facts kb)))

(defun eval-builtin (kb pattern bindings support)
  "Evaluate a built-in condition (variables already substituted).
Returns (values ok bindings support)."
  (let ((op (first pattern)))
    (case op
      (different
       (destructuring-bind (a b) (rest pattern)
         (values (and (ground-p a) (ground-p b) (not (equal a b)))
                 bindings support)))
      ((lt gt le ge)
       (destructuring-bind (a b) (rest pattern)
         (values (and (integerp a) (integerp b)
                      (ecase op
                        (lt (< a b))
                        (gt (> a b))
                        (le (<= a b))
                        (ge (>= a b))))
                 bindings support)))
      ((add sub mul)
       (destructuring-bind (a b c) (rest pattern)
         (if (and (integerp a) (integerp b))
             (let* ((value (ecase op
                             (add (+ a b))
                             (sub (- a b))
                             (mul (* a b))))
                    (new (match c value bindings)))
               (if (eq new :fail)
                   (values nil bindings support)
                   (values t new support)))
             (values nil bindings support))))
      (not
       (let ((inner (second pattern)))
         (if (and (consp inner) (ground-p inner) (not (known-p kb inner)))
             (values t bindings (cons pattern support))
             (values nil bindings support))))
      (t (values nil bindings support)))))

(defun satisfy (kb conditions bindings support)
  "All ways to satisfy CONDITIONS: a list of (bindings . supporting-facts)."
  (if (null conditions)
      (list (cons bindings (reverse support)))
      (let ((pattern (substitute-bindings (first conditions) bindings)))
        (if (builtin-condition-p pattern)
            (multiple-value-bind (ok new-bindings new-support)
                (eval-builtin kb pattern bindings support)
              (if ok
                  (satisfy kb (rest conditions) new-bindings new-support)
                  '()))
            (let ((results '()))
              (dolist (fact (candidate-facts kb pattern))
                (let ((b (match pattern fact bindings)))
                  (unless (eq b :fail)
                    (dolist (r (satisfy kb (rest conditions) b (cons fact support)))
                      (push r results)))))
              (nreverse results))))))

(defun run-rules (kb rules max-rounds max-facts)
  "Apply RULES until nothing new appears or a limit is hit.
Returns (values new-facts reason): :fixpoint, :round-limit or :fact-limit."
  (let ((derived '()))
    (dotimes (round max-rounds)
      (declare (ignorable round))
      (let ((changed nil))
        (dolist (rule rules)
          (dolist (found (satisfy kb (rule-conditions rule) '() '()))
            (let ((fact (substitute-bindings (rule-conclusion rule) (car found))))
              (when (add-fact kb fact (list :derived (rule-name rule) (cdr found)))
                (push fact derived)
                (setf changed t)
                (when (>= (length (kb-facts kb)) max-facts)
                  (return-from run-rules
                    (values (nreverse derived) :fact-limit)))))))
        (unless changed
          (return-from run-rules (values (nreverse derived) :fixpoint)))))
    (values (nreverse derived) :round-limit)))

(defun rule-uses-negation-p (rule)
  (some (lambda (condition)
          (and (consp condition) (eq (first condition) 'not)))
        (rule-conditions rule)))

(defun negation-conflicts (kb)
  "Derived facts that relied on a NOT whose fact has since become known."
  (let ((bad '()))
    (maphash (lambda (fact why)
               (when (eq (first why) :derived)
                 (dolist (support (third why))
                   (when (and (consp support)
                              (eq (first support) 'not)
                              (known-p kb (second support)))
                     (push fact bad)))))
             (kb-why kb))
    bad))

(defun forward-chain (kb &key (max-rounds *max-rounds*) (max-facts *max-facts*))
  "Apply rules until nothing new appears or a limit is hit. Rules that use NOT
run in a second phase, after all the other rules have settled.
Returns (values new-facts reason): :fixpoint, :round-limit, :fact-limit or
:negation-conflict (a NOT assumption was contradicted by a later fact)."
  (let ((negating (remove-if-not #'rule-uses-negation-p (kb-rules kb))))
    (multiple-value-bind (derived reason)
        (run-rules kb (remove-if #'rule-uses-negation-p (kb-rules kb))
                   max-rounds max-facts)
      (if (or (null negating) (not (eq reason :fixpoint)))
          (values derived reason)
          (multiple-value-bind (more more-reason)
              (run-rules kb (kb-rules kb) max-rounds max-facts)
            (values (append derived more)
                    (if (and (eq more-reason :fixpoint) (negation-conflicts kb))
                        :negation-conflict
                        more-reason)))))))

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
    (cond ((and (consp fact) (eq (first fact) 'not))
           (format stream "~a~a -- no such fact is known (negation as failure)~%"
                   pad (show fact)))
          ((null why)
           (format stream "~a~a -- not known~%" pad (show fact)))
          ((eq (first why) :given)
           (format stream "~a~a -- given~%" pad (show fact)))
          (t
           (format stream "~a~a -- derived by rule ~(~a~)~%"
                   pad (show fact) (second why))
           (dolist (support (third why))
             (explain kb support :stream stream :depth (1+ depth)))))))

;;; Retraction ("what if this stopped being true?")

(defun given-facts (kb)
  (remove-if-not (lambda (fact)
                   (eq (first (gethash fact (kb-why kb))) :given))
                 (kb-facts kb)))

(defun clear-kb-facts (kb)
  (setf (kb-facts kb) '())
  (clrhash (kb-why kb))
  (clrhash (kb-index kb)))

(defun retract-fact (kb fact)
  "Remove the given FACT and every derived fact that depended on it by
rebuilding the derived facts from the remaining given facts.
Returns the facts that disappeared, or NIL if FACT is not a given fact."
  (let ((why (gethash fact (kb-why kb))))
    (when (and why (eq (first why) :given))
      (let ((before (kb-facts kb))
            (keep (remove fact (given-facts kb) :test #'equal)))
        (clear-kb-facts kb)
        (dolist (kept keep)
          (add-fact kb kept))
        (forward-chain kb)
        (remove-if (lambda (old) (known-p kb old)) before)))))

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
               (then (cousin ?a ?b)))))

    ;; ---- Generic rules that work on any relation named in the facts ----

    (:id "L007" :title "Generic transitivity"
     :why "Any relation declared with transitive-relation is chained automatically (a to b and b to c gives a to c)."
     :forms ((rule generic-transitive-rule
               (if (transitive-relation ?r) (?r ?a ?b) (?r ?b ?c))
               (then (?r ?a ?c)))))

    (:id "L008" :title "Generic symmetry"
     :why "Any relation declared with symmetric-relation works in both directions."
     :forms ((rule generic-symmetric-rule
               (if (symmetric-relation ?r) (?r ?a ?b))
               (then (?r ?b ?a)))))

    (:id "L009" :title "Generic inverse"
     :why "inverse-relation facts such as (inverse-relation depends-on prerequisite-of) create the reverse relation automatically."
     :forms ((rule generic-inverse-rule
               (if (inverse-relation ?r ?s) (?r ?a ?b))
               (then (?s ?b ?a)))))

    ;; ---- Assistant skills: rooms, devices, status, schedule, permissions ----

    (:id "L010" :title "Rooms and devices"
     :why "Starter home model: which devices are in which rooms, and what kind each one is."
     :forms ((fact (device-in lamp-1 lounge))
             (fact (device-in lamp-2 study))
             (fact (device-in heater lounge))
             (fact (device-in speaker-1 study))
             (fact (device-type lamp-1 light))
             (fact (device-type lamp-2 light))
             (fact (device-type heater climate))
             (fact (device-type speaker-1 audio))
             (rule room-contains-rule
               (if (device-in ?d ?r))
               (then (room-contains ?r ?d)))))

    (:id "L011" :title "Device lookups"
     :why "Answers what kinds of device a room has and which lights are in which room."
     :forms ((rule room-has-type-rule
               (if (device-in ?d ?r) (device-type ?d ?t))
               (then (room-has-type ?r ?t)))
             (rule light-in-rule
               (if (device-in ?d ?r) (device-type ?d light))
               (then (light-in ?d ?r)))))

    (:id "L012" :title "Presence and lights"
     :why "Knows who is in which room and suggests turning on the lights where someone is; explain shows why."
     :forms ((fact (at ana study))
             (fact (at ben lounge))
             (rule occupied-rule
               (if (at ?p ?r))
               (then (occupied ?r)))
             (rule suggest-light-rule
               (if (at ?p ?r) (light-in ?d ?r))
               (then (suggest turn-on ?d)))))

    (:id "L013" :title "Preferences"
     :why "Uses what people prefer to suggest playing music for one person and muting the speaker for another."
     :forms ((fact (prefers ana quiet))
             (fact (prefers ben music))
             (fact (device-in speaker-2 lounge))
             (fact (device-type speaker-2 audio))
             (rule suggest-music-rule
               (if (at ?p ?r) (prefers ?p music) (device-in ?d ?r) (device-type ?d audio))
               (then (suggest play-music ?d)))
             (rule suggest-mute-rule
               (if (at ?p ?r) (prefers ?p quiet) (device-in ?d ?r) (device-type ?d audio))
               (then (suggest mute ?d)))))

    (:id "L014" :title "System components"
     :why "Which parts of a system need which other parts; chains are followed using the generic transitivity rule."
     :forms ((fact (needs cooling power))
             (fact (needs compute power))
             (fact (needs compute cooling))
             (fact (needs network power))
             (fact (needs assistant compute))
             (fact (needs assistant network))
             (fact (transitive-relation needs))))

    (:id "L015" :title "Status and failures"
     :why "A demo status report: when a component is down, everything that needs it is marked degraded, and explain shows the chain."
     :forms ((fact (status power ok))
             (fact (status cooling ok))
             (fact (status compute ok))
             (fact (status network down))
             (rule failing-rule
               (if (status ?c down))
               (then (failing ?c)))
             (rule degraded-rule
               (if (status ?c down) (needs ?s ?c))
               (then (degraded ?s)))))

    (:id "L016" :title "Alerts"
     :why "Turns failures into critical alerts and degraded systems into warnings."
     :forms ((rule alert-failing-rule
               (if (failing ?c))
               (then (alert ?c critical)))
             (rule alert-degraded-rule
               (if (degraded ?s))
               (then (alert ?s warning)))))

    (:id "L017" :title "Calendar"
     :why "Events, their time slots, and who attends; works out when each person is busy."
     :forms ((fact (scheduled standup mon-9))
             (fact (scheduled review mon-9))
             (fact (scheduled lunch mon-12))
             (fact (attends ana standup))
             (fact (attends ana review))
             (fact (attends ben standup))
             (fact (attends ben lunch))
             (rule busy-rule
               (if (attends ?p ?e) (scheduled ?e ?t))
               (then (busy ?p ?t)))))

    (:id "L018" :title "Schedule clashes"
     :why "Flags a person who attends two different events in the same time slot."
     :forms ((rule clash-rule
               (if (attends ?p ?a) (attends ?p ?b) (scheduled ?a ?t) (scheduled ?b ?t) (different ?a ?b))
               (then (clash ?p ?a ?b)))))

    (:id "L019" :title "Roles and permissions"
     :why "Who holds which role and what each role allows, so the assistant can say who may do what."
     :forms ((fact (user-role ana admin))
             (fact (user-role ben editor))
             (fact (user-role cai viewer))
             (fact (role-grants admin manage))
             (fact (role-grants editor edit))
             (fact (role-grants viewer view))
             (rule permission-rule
               (if (user-role ?u ?r) (role-grants ?r ?p))
               (then (permitted ?u ?p)))))

    (:id "L020" :title "Role hierarchy"
     :why "Higher roles inherit everything lower roles are allowed to do."
     :forms ((fact (role-inherits admin editor))
             (fact (role-inherits editor viewer))
             (fact (transitive-relation role-inherits))
             (rule role-inherits-grants-rule
               (if (role-inherits ?r ?s) (role-grants ?s ?p))
               (then (role-grants ?r ?p)))))

    (:id "L021" :title "Task dependencies"
     :why "Which tasks depend on which; indirect dependencies and the reverse relation are derived automatically."
     :forms ((fact (depends-on test build))
             (fact (depends-on build compile))
             (fact (depends-on deploy test))
             (fact (depends-on bundle build))
             (fact (transitive-relation depends-on))
             (fact (inverse-relation depends-on prerequisite-of))))

    (:id "L022" :title "Task progress"
     :why "Notes finished work and shows which tasks have a finished prerequisite."
     :forms ((fact (done compile))
             (rule has-done-prerequisite-rule
               (if (done ?y) (depends-on ?x ?y))
               (then (has-done-prerequisite ?x ?y)))))

    ;; ---- Family: more people and relations ----

    (:id "L023" :title "More family members"
     :why "Gives the family rules more people to work on."
     :forms ((fact (parent bob ivy))
             (fact (parent erin frank))
             (fact (parent erin grace))
             (fact (parent dave hank))))

    (:id "L024" :title "Gender facts"
     :why "Records who is female or male so relations can be named precisely."
     :forms ((fact (female alice))
             (fact (female erin))
             (fact (female carol))
             (fact (female ivy))
             (fact (female grace))
             (fact (male bob))
             (fact (male dave))
             (fact (male frank))
             (fact (male hank))))

    (:id "L025" :title "Mother and father"
     :why "A female parent is a mother and a male parent is a father."
     :forms ((rule mother-rule
               (if (parent ?p ?c) (female ?p))
               (then (mother ?p ?c)))
             (rule father-rule
               (if (parent ?p ?c) (male ?p))
               (then (father ?p ?c)))))

    (:id "L026" :title "Brother and sister"
     :why "A male sibling is a brother and a female sibling is a sister."
     :forms ((rule brother-rule
               (if (sibling ?a ?b) (male ?a))
               (then (brother ?a ?b)))
             (rule sister-rule
               (if (sibling ?a ?b) (female ?a))
               (then (sister ?a ?b)))))

    (:id "L027" :title "Grandmother and grandfather"
     :why "Grandparents named by gender."
     :forms ((rule grandmother-rule
               (if (grandparent ?g ?c) (female ?g))
               (then (grandmother ?g ?c)))
             (rule grandfather-rule
               (if (grandparent ?g ?c) (male ?g))
               (then (grandfather ?g ?c)))))

    (:id "L028" :title "Aunt and uncle"
     :why "A female pibling is an aunt and a male pibling is an uncle."
     :forms ((rule aunt-rule
               (if (pibling ?a ?c) (female ?a))
               (then (aunt ?a ?c)))
             (rule uncle-rule
               (if (pibling ?a ?c) (male ?a))
               (then (uncle ?a ?c)))))

    (:id "L029" :title "Child and descendant"
     :why "The reverse of parent and of ancestor."
     :forms ((rule child-rule
               (if (parent ?p ?c))
               (then (child ?c ?p)))
             (rule descendant-rule
               (if (ancestor ?a ?d))
               (then (descendant ?d ?a)))))

    (:id "L030" :title "Great-grandparent"
     :why "A parent of a grandparent."
     :forms ((rule great-grandparent-rule
               (if (parent ?a ?b) (grandparent ?b ?c))
               (then (great-grandparent ?a ?c)))))

    (:id "L031" :title "Marriage and in-laws"
     :why "Marriage works in both directions; the parent of someone's spouse is a parent-in-law."
     :forms ((fact (married alice leo))
             (fact (married bob nina))
             (fact (married dave olga))
             (fact (symmetric-relation married))
             (rule parent-in-law-rule
               (if (parent ?p ?a) (married ?a ?b))
               (then (parent-in-law ?p ?b)))))

    (:id "L032" :title "Second parents"
     :why "Adds the other parent for several children."
     :forms ((fact (parent leo bob))
             (fact (parent leo erin))
             (fact (parent nina carol))
             (fact (parent nina ivy))
             (fact (parent olga hank))
             (fact (male leo))
             (fact (female nina))
             (fact (female olga))))

    (:id "L033" :title "Co-parents"
     :why "Two different people who are parents of the same child."
     :forms ((rule co-parent-rule
               (if (parent ?a ?c) (parent ?b ?c) (different ?a ?b))
               (then (co-parent ?a ?b)))))

    ;; ---- General knowledge: animals, friends, graphs, numbers, places, time ----

    (:id "L034" :title "More animals"
     :why "Extends the animal taxonomy with more kinds and a fish and amphibian branch."
     :forms ((fact (is-a horse mammal))
             (fact (is-a bat mammal))
             (fact (is-a eagle bird))
             (fact (is-a penguin bird))
             (fact (is-a fish animal))
             (fact (is-a salmon fish))
             (fact (is-a shark fish))
             (fact (is-a frog amphibian))
             (fact (is-a amphibian animal))))

    (:id "L035" :title "More properties"
     :why "More traits that animals inherit from their categories."
     :forms ((fact (has fish gills))
             (fact (has fish fins))
             (fact (has bird wings))
             (fact (has mammal milk))
             (fact (has amphibian moist-skin))))

    (:id "L036" :title "Abilities"
     :why "What animals can do; abilities of a category pass down to its members. Flying is listed per animal because not every bird flies."
     :forms ((fact (can sparrow fly))
             (fact (can eagle fly))
             (fact (can bat fly))
             (fact (can fish swim))
             (fact (can penguin swim))
             (fact (can bird lay-eggs))
             (fact (can mammal nurse-young))
             (rule can-inherit-rule
               (if (is-a ?x ?y) (can ?y ?a))
               (then (can ?x ?a)))))

    (:id "L037" :title "Friendship"
     :why "Friendship works both ways; a friend of a friend is a possible introduction."
     :forms ((fact (friend-of ana ben))
             (fact (friend-of ben cai))
             (fact (friend-of cai dee))
             (fact (friend-of eli fay))
             (fact (symmetric-relation friend-of))
             (rule friend-of-friend-rule
               (if (friend-of ?a ?b) (friend-of ?b ?c) (different ?a ?c))
               (then (friend-of-friend ?a ?c)))))

    (:id "L038" :title "Graph reachability"
     :why "A small network of nodes; works out which nodes can be reached from which."
     :forms ((fact (edge n1 n2))
             (fact (edge n2 n3))
             (fact (edge n3 n4))
             (fact (edge n1 n5))
             (fact (edge n5 n6))
             (fact (edge n6 n3))
             (rule reach-direct-rule
               (if (edge ?a ?b))
               (then (reachable ?a ?b)))
             (rule reach-step-rule
               (if (edge ?a ?b) (reachable ?b ?c))
               (then (reachable ?a ?c)))))

    (:id "L039" :title "Shared destinations"
     :why "Two different nodes that can both reach the same node."
     :forms ((rule common-target-rule
               (if (reachable ?a ?t) (reachable ?b ?t) (different ?a ?b))
               (then (shares-target ?a ?b)))))

    (:id "L040" :title "Successor numbers"
     :why "Counting from 1 to 6 using next facts; less-than is built from them and chained by the generic transitivity rule."
     :forms ((fact (next 1 2))
             (fact (next 2 3))
             (fact (next 3 4))
             (fact (next 4 5))
             (fact (next 5 6))
             (fact (transitive-relation less-than))
             (rule less-than-base-rule
               (if (next ?a ?b))
               (then (less-than ?a ?b)))))

    (:id "L041" :title "Greater-than and between"
     :why "The reverse of less-than, plus a between relation for three ordered numbers."
     :forms ((fact (inverse-relation less-than greater-than))
             (rule between-rule
               (if (less-than ?a ?b) (less-than ?b ?c))
               (then (between ?b ?a ?c)))))

    (:id "L042" :title "Ranking people"
     :why "Height ordering: taller-than chains together and has a shorter-than reverse."
     :forms ((fact (taller-than ana ben))
             (fact (taller-than ben cai))
             (fact (taller-than cai dee))
             (fact (transitive-relation taller-than))
             (fact (inverse-relation taller-than shorter-than))))

    (:id "L043" :title "Places"
     :why "Where places are, nested from city to country to continent; located-in is chained automatically."
     :forms ((fact (located-in singapore asia))
             (fact (located-in tokyo japan))
             (fact (located-in kyoto japan))
             (fact (located-in japan asia))
             (fact (located-in paris france))
             (fact (located-in france europe))
             (fact (located-in asia earth))
             (fact (located-in europe earth))
             (fact (transitive-relation located-in))))

    (:id "L044" :title "Capitals"
     :why "A capital is a city and is located in its country."
     :forms ((fact (capital-of tokyo japan))
             (fact (capital-of paris france))
             (rule capital-located-rule
               (if (capital-of ?c ?n))
               (then (located-in ?c ?n)))
             (rule capital-city-rule
               (if (capital-of ?c ?n))
               (then (city ?c)))))

    (:id "L045" :title "Same country"
     :why "Two different places inside the same country."
     :forms ((fact (country japan))
             (fact (country france))
             (rule same-country-rule
               (if (located-in ?a ?c) (located-in ?b ?c) (country ?c) (different ?a ?b))
               (then (same-country ?a ?b)))))

    (:id "L046" :title "Before and after"
     :why "Ordering of events in a day; before chains together and has an after reverse."
     :forms ((fact (before breakfast lunch))
             (fact (before lunch dinner))
             (fact (before dinner sleep))
             (fact (transitive-relation before))
             (fact (inverse-relation before after))))

    (:id "L047" :title "Disjoint categories and conflicts"
     :why "Some categories cannot overlap; if something is placed in two of them, a conflict is reported."
     :forms ((fact (disjoint mammal bird))
             (fact (disjoint mammal fish))
             (fact (disjoint bird fish))
             (fact (disjoint mammal amphibian))
             (fact (symmetric-relation disjoint))
             (rule conflict-rule
               (if (disjoint ?a ?b) (is-a ?x ?a) (is-a ?x ?b))
               (then (conflict ?x ?a ?b)))))

    (:id "L048" :title "Courses"
     :why "Teachers, enrolled students, who studies under whom, and who shares a class."
     :forms ((fact (teaches smith math))
             (fact (teaches jones physics))
             (fact (enrolled ana math))
             (fact (enrolled ben math))
             (fact (enrolled ben physics))
             (rule student-of-rule
               (if (enrolled ?s ?c) (teaches ?t ?c))
               (then (student-of ?s ?t)))
             (rule classmates-rule
               (if (enrolled ?a ?c) (enrolled ?b ?c) (different ?a ?b))
               (then (classmates ?a ?b)))))

    (:id "L049" :title "Parts and wholes"
     :why "What is part of what; chained so a spoke is part of the bike, with a has-part reverse."
     :forms ((fact (part-of wheel bike))
             (fact (part-of frame bike))
             (fact (part-of spoke wheel))
             (fact (part-of rim wheel))
             (fact (transitive-relation part-of))
             (fact (inverse-relation part-of has-part))))

    ;; ---- More assistant skills: moods, state, security, deadlines, people ----

    (:id "L050" :title "Time of day and lighting"
     :why "A demo time of day; in the evening the assistant suggests dimming the lights in occupied rooms."
     :forms ((fact (time-of-day evening))
             (rule evening-dim-rule
               (if (time-of-day evening) (at ?p ?r) (light-in ?d ?r))
               (then (suggest dim ?d)))))

    (:id "L051" :title "Device capabilities"
     :why "What each kind of device can do, so the assistant can say what a particular device is able to do."
     :forms ((fact (type-can light dim))
             (fact (type-can light switch))
             (fact (type-can audio play-music))
             (fact (type-can climate heat))
             (rule device-can-rule
               (if (device-type ?d ?t) (type-can ?t ?a))
               (then (device-can ?d ?a)))))

    (:id "L052" :title "Device state"
     :why "Demo on/off readings for devices, and which rooms currently have a light on."
     :forms ((fact (state lamp-1 off))
             (fact (state lamp-2 off))
             (fact (state heater on))
             (rule device-on-rule
               (if (state ?d on))
               (then (is-on ?d)))
             (rule lit-rule
               (if (is-on ?d) (device-type ?d light) (device-in ?d ?r))
               (then (lit ?r)))))

    (:id "L053" :title "Energy saving"
     :why "Adds a kitchen with a lamp left on in an empty room; the assistant suggests switching off anything that is on in an empty room."
     :forms ((fact (device-in lamp-3 kitchen))
             (fact (device-type lamp-3 light))
             (fact (state lamp-3 on))
             (fact (occupancy kitchen empty))
             (rule energy-saving-rule
               (if (occupancy ?r empty) (device-in ?d ?r) (state ?d on))
               (then (suggest turn-off ?d)))))

    (:id "L054" :title "Security"
     :why "Demo door readings: when security is armed, an unlocked door raises a warning and a suggestion to lock it."
     :forms ((fact (door-state front-door locked))
             (fact (door-state back-door unlocked))
             (fact (security-mode armed))
             (rule unlocked-while-armed-rule
               (if (security-mode armed) (door-state ?d unlocked))
               (then (alert ?d warning)))
             (rule suggest-lock-rule
               (if (security-mode armed) (door-state ?d unlocked))
               (then (suggest lock ?d)))))

    (:id "L055" :title "Days of the week"
     :why "Orders the days of the week; earlier-day is chained automatically by the generic transitivity rule."
     :forms ((fact (next-day mon tue))
             (fact (next-day tue wed))
             (fact (next-day wed thu))
             (fact (next-day thu fri))
             (fact (next-day fri sat))
             (fact (next-day sat sun))
             (fact (transitive-relation earlier-day))
             (rule earlier-day-base-rule
               (if (next-day ?a ?b))
               (then (earlier-day ?a ?b)))))

    (:id "L056" :title "Deadlines and reminders"
     :why "Demo tasks with owners and due days; the assistant works out what is overdue and who to remind."
     :forms ((fact (today wed))
             (fact (due report mon))
             (fact (due taxes fri))
             (fact (owns ana report))
             (fact (owns ben taxes))
             (rule overdue-rule
               (if (due ?t ?d) (today ?n) (earlier-day ?d ?n))
               (then (overdue ?t)))
             (rule remind-rule
               (if (owns ?p ?t) (due ?t ?d))
               (then (remind ?p ?t ?d)))
             (rule overdue-remind-rule
               (if (overdue ?t) (owns ?p ?t))
               (then (remind-overdue ?p ?t)))))

    (:id "L057" :title "Priorities"
     :why "Marks task priorities; an overdue high-priority task is urgent, and owners of high-priority tasks are told to focus on them."
     :forms ((fact (priority report high))
             (fact (priority taxes medium))
             (rule urgent-rule
               (if (overdue ?t) (priority ?t high))
               (then (urgent ?t)))
             (rule focus-rule
               (if (priority ?t high) (owns ?p ?t))
               (then (focus ?p ?t)))))

    (:id "L058" :title "Shopping and stock"
     :why "Demo pantry levels; anything running low becomes a suggestion to buy it."
     :forms ((fact (stock milk low))
             (fact (stock rice ok))
             (fact (stock coffee low))
             (rule restock-rule
               (if (stock ?i low))
               (then (suggest buy ?i)))))

    (:id "L059" :title "Weather and plans"
     :why "Demo forecast and plans; people with outdoor plans on a rainy day get an umbrella suggestion."
     :forms ((fact (forecast tomorrow rain))
             (fact (plans ana tomorrow outdoors))
             (fact (plans ben tomorrow indoors))
             (rule umbrella-rule
               (if (forecast ?d rain) (plans ?p ?d outdoors))
               (then (suggest bring-umbrella ?p)))))

    (:id "L060" :title "Organisation chart"
     :why "Who directly manages whom; management chains and reporting lines are derived automatically, and peers share the same direct manager."
     :forms ((fact (manages-directly rhea tom))
             (fact (manages-directly tom uma))
             (fact (manages-directly tom vic))
             (fact (manages-directly uma wes))
             (fact (transitive-relation manages))
             (fact (inverse-relation manages reports-to))
             (rule manages-base-rule
               (if (manages-directly ?m ?a))
               (then (manages ?m ?a)))
             (rule peers-rule
               (if (manages-directly ?m ?a) (manages-directly ?m ?b) (different ?a ?b))
               (then (peers ?a ?b)))))

    (:id "L061" :title "Transit network"
     :why "Stations joined by lines; the assistant works out which stations can be reached from which."
     :forms ((fact (connected central north))
             (fact (connected central east))
             (fact (connected east harbour))
             (fact (connected harbour airport))
             (fact (symmetric-relation connected))
             (fact (transitive-relation can-travel))
             (rule can-travel-base-rule
               (if (connected ?a ?b))
               (then (can-travel ?a ?b)))))

    (:id "L062" :title "What the assistant can do"
     :why "A small self-description: the assistant lists the topics it can help with."
     :forms ((fact (skill assistant home-control))
             (fact (skill assistant scheduling))
             (fact (skill assistant diagnostics))
             (fact (skill assistant explanations))
             (fact (topic-of home-control lights))
             (fact (topic-of home-control music))
             (fact (topic-of scheduling meetings))
             (fact (topic-of diagnostics system-status))
             (rule can-help-rule
               (if (skill assistant ?s) (topic-of ?s ?t))
               (then (can-help-with ?t)))))

    ;; ---- More general knowledge ----

    (:id "L063" :title "Programming languages"
     :why "Lisp dialects and their implementations; an implementation of a dialect is also an implementation of the wider family."
     :forms ((fact (dialect-of common-lisp lisp))
             (fact (dialect-of scheme lisp))
             (fact (dialect-of clojure lisp))
             (fact (implementation-of sbcl common-lisp))
             (fact (implementation-of ecl common-lisp))
             (fact (implementation-of clisp common-lisp))
             (rule implementation-family-rule
               (if (implementation-of ?i ?d) (dialect-of ?d ?l))
               (then (implementation-of ?i ?l)))))

    (:id "L064" :title "Solar system"
     :why "What orbits what; in-system-of follows the chain, so a moon is in the system of the Sun."
     :forms ((fact (orbits mercury sun))
             (fact (orbits venus sun))
             (fact (orbits earth sun))
             (fact (orbits mars sun))
             (fact (orbits moon earth))
             (fact (orbits phobos mars))
             (fact (transitive-relation in-system-of))
             (rule in-system-base-rule
               (if (orbits ?a ?b))
               (then (in-system-of ?a ?b)))))

    (:id "L065" :title "Kinds of number"
     :why "Number kinds nested inside each other, using the same is-a chaining as the animals."
     :forms ((fact (is-a natural-number integer))
             (fact (is-a integer rational))
             (fact (is-a rational real))
             (fact (is-a prime natural-number))))

    (:id "L066" :title "Shapes"
     :why "A taxonomy of shapes with traits that pass down, so a square inherits what quadrilaterals and parallelograms have."
     :forms ((fact (is-a square rectangle))
             (fact (is-a square rhombus))
             (fact (is-a rectangle parallelogram))
             (fact (is-a rhombus parallelogram))
             (fact (is-a parallelogram quadrilateral))
             (fact (is-a quadrilateral polygon))
             (fact (is-a triangle polygon))
             (fact (has quadrilateral four-sides))
             (fact (has triangle three-sides))
             (fact (has parallelogram parallel-opposite-sides))))

    (:id "L067" :title "Shape traits"
     :why "More traits, plus a rule that triangles and quadrilaterals cannot overlap."
     :forms ((fact (has rectangle right-angles))
             (fact (has rhombus equal-sides))
             (fact (disjoint triangle quadrilateral))))

    (:id "L068" :title "Colour mixing"
     :why "Which colours mix to make which; the order of the two colours does not matter."
     :forms ((fact (mix red blue purple))
             (fact (mix red yellow orange))
             (fact (mix blue yellow green))
             (rule mix-symmetric-rule
               (if (mix ?a ?b ?c))
               (then (mix ?b ?a ?c)))))

    (:id "L069" :title "Food chain"
     :why "Who eats whom; food-chain follows the whole chain from predator down to plants."
     :forms ((fact (eats hawk snake))
             (fact (eats snake frog))
             (fact (eats frog insect))
             (fact (eats insect plant))
             (fact (transitive-relation food-chain))
             (rule food-chain-base-rule
               (if (eats ?a ?b))
               (then (food-chain ?a ?b)))))

    (:id "L070" :title "Habitats"
     :why "Where animals live; an animal living in a water habitat is aquatic."
     :forms ((fact (lives-in frog pond))
             (fact (lives-in salmon river))
             (fact (lives-in shark ocean))
             (fact (lives-in eagle mountain))
             (fact (water-habitat pond))
             (fact (water-habitat river))
             (fact (water-habitat ocean))
             (rule aquatic-rule
               (if (lives-in ?a ?h) (water-habitat ?h))
               (then (aquatic ?a)))))

    ;; ---- Lessons that use the Phase 1 engine: not, comparisons, arithmetic ----

    (:id "L071" :title "Empty rooms"
     :why "Lists the rooms and uses negation: a room nobody is in is empty."
     :forms ((fact (room lounge))
             (fact (room study))
             (fact (room kitchen))
             (rule empty-room-rule
               (if (room ?r) (not (occupied ?r)))
               (then (empty-room ?r)))))

    (:id "L072" :title "Wasted energy"
     :why "Anything switched on in an empty room becomes a suggestion to switch it off, worked out from who is where."
     :forms ((rule wasted-energy-rule
               (if (empty-room ?r) (device-in ?d ?r) (state ?d on))
               (then (suggest turn-off ?d)))))

    (:id "L073" :title "Unattended appliances"
     :why "Adds an oven left on in the kitchen; an appliance that is on in an empty room raises a warning."
     :forms ((fact (device-in oven kitchen))
             (fact (device-type oven appliance))
             (fact (state oven on))
             (rule unattended-appliance-rule
               (if (device-type ?d appliance) (state ?d on) (device-in ?d ?r) (not (occupied ?r)))
               (then (alert ?d unattended)))))

    (:id "L074" :title "Event times"
     :why "Start hours and lengths for the Monday events; arithmetic works out when each one ends."
     :forms ((fact (starts standup 9))
             (fact (lasts standup 1))
             (fact (starts review 9))
             (fact (lasts review 2))
             (fact (starts lunch 12))
             (fact (lasts lunch 1))
             (rule ends-rule
               (if (starts ?e ?s) (lasts ?e ?d) (add ?s ?d ?end))
               (then (ends ?e ?end)))))

    (:id "L075" :title "Overlapping events"
     :why "Two different events overlap when each one starts before the other ends."
     :forms ((rule overlap-rule
               (if (starts ?a ?s1) (ends ?a ?e1) (starts ?b ?s2) (ends ?b ?e2) (different ?a ?b) (lt ?s1 ?e2) (lt ?s2 ?e1))
               (then (overlaps ?a ?b)))))

    (:id "L076" :title "Battery levels"
     :why "Demo battery readings; a device below the low-battery threshold gets an alert and a charging suggestion."
     :forms ((fact (battery phone 15))
             (fact (battery tablet 80))
             (fact (battery watch 8))
             (fact (threshold low-battery 20))
             (rule low-battery-rule
               (if (battery ?d ?level) (threshold low-battery ?t) (lt ?level ?t))
               (then (alert ?d low-battery)))
             (rule suggest-charge-rule
               (if (alert ?d low-battery))
               (then (suggest charge ?d)))))

    (:id "L077" :title "Thermostat"
     :why "Demo room temperatures against a comfort range; an occupied room that is too cold raises an alert."
     :forms ((fact (temperature lounge 17))
             (fact (temperature study 22))
             (fact (comfort lowest 19))
             (fact (comfort highest 24))
             (rule too-cold-rule
               (if (temperature ?r ?t) (comfort lowest ?m) (lt ?t ?m))
               (then (too-cold ?r)))
             (rule too-warm-rule
               (if (temperature ?r ?t) (comfort highest ?m) (gt ?t ?m))
               (then (too-warm ?r)))
             (rule cold-alert-rule
               (if (too-cold ?r) (occupied ?r))
               (then (alert ?r too-cold)))))

    (:id "L078" :title "Countdowns"
     :why "Demo due dates as day numbers; subtraction gives the days left, and the assistant flags what is due soon or already past due."
     :forms ((fact (current-date 15))
             (fact (due-date taxes 20))
             (fact (due-date passport 40))
             (fact (due-date rent 10))
             (rule days-left-rule
               (if (due-date ?t ?d) (current-date ?n) (sub ?d ?n ?left))
               (then (days-left ?t ?left)))
             (rule due-soon-rule
               (if (days-left ?t ?x) (ge ?x 0) (lt ?x 8))
               (then (due-soon ?t)))
             (rule past-due-rule
               (if (days-left ?t ?x) (lt ?x 0))
               (then (past-due ?t)))))

    (:id "L079" :title "Budget"
     :why "A demo budget; subtraction gives what is left in each category and anything below zero is over budget."
     :forms ((fact (spent food 120))
             (fact (spent transport 45))
             (fact (spent fun 80))
             (fact (budget food 150))
             (fact (budget transport 60))
             (fact (budget fun 60))
             (rule remaining-rule
               (if (spent ?c ?s) (budget ?c ?b) (sub ?b ?s ?left))
               (then (remaining ?c ?left)))
             (rule over-budget-rule
               (if (remaining ?c ?left) (lt ?left 0))
               (then (over-budget ?c)))
             (rule budget-alert-rule
               (if (over-budget ?c))
               (then (alert ?c over-budget)))))

    (:id "L080" :title "Unreported components"
     :why "Uses negation to notice components that have no status report at all, and raises an alert for each."
     :forms ((fact (component power))
             (fact (component cooling))
             (fact (component compute))
             (fact (component network))
             (fact (component assistant))
             (rule reported-rule
               (if (status ?c ?s))
               (then (status-reported ?c)))
             (rule unreported-rule
               (if (component ?c) (not (status-reported ?c)))
               (then (unreported ?c)))
             (rule unreported-alert-rule
               (if (unreported ?c))
               (then (alert ?c no-status)))))

    (:id "L081" :title "Open tasks"
     :why "Lists the tasks and uses negation: a task that is not marked done is open."
     :forms ((fact (task compile))
             (fact (task build))
             (fact (task test))
             (fact (task deploy))
             (fact (task bundle))
             (rule open-task-rule
               (if (task ?t) (not (done ?t)))
               (then (open-task ?t)))))

    (:id "L082" :title "Ready tasks"
     :why "A task is blocked if anything it depends on is not done; an open task that is not blocked is ready to start."
     :forms ((rule blocked-rule
               (if (depends-on ?t ?p) (not (done ?p)))
               (then (blocked ?t)))
             (rule ready-rule
               (if (open-task ?t) (not (blocked ?t)))
               (then (ready ?t)))))

    (:id "L083" :title "People without access"
     :why "Uses negation to find people who have no permission at all."
     :forms ((fact (person ana))
             (fact (person ben))
             (fact (person cai))
             (fact (person dee))
             (rule has-any-permission-rule
               (if (permitted ?p ?x))
               (then (has-any-permission ?p)))
             (rule no-access-rule
               (if (person ?p) (not (has-any-permission ?p)))
               (then (no-access ?p)))))

    (:id "L084" :title "Counting"
     :why "Counts from 0 to 5 using arithmetic; the comparison stops the rule so it always finishes."
     :forms ((fact (tick 0))
             (rule tick-rule
               (if (tick ?n) (lt ?n 5) (add ?n 1 ?m))
               (then (tick ?m)))))

    (:id "L085" :title "Squares"
     :why "Squares of the counted numbers, using multiplication."
     :forms ((rule square-rule
               (if (tick ?n) (mul ?n ?n ?sq))
               (then (square ?n ?sq)))))

    (:id "L086" :title "Planets and moons"
     :why "Planets and moons as kinds, with a trait that moons inherit."
     :forms ((fact (is-a mercury planet))
             (fact (is-a venus planet))
             (fact (is-a earth planet))
             (fact (is-a mars planet))
             (fact (is-a moon satellite))
             (fact (is-a phobos satellite))
             (fact (has satellite orbit-around-planet))))

    (:id "L087" :title "Musical notes"
     :why "The seven note names in order; lower-note chains them so any earlier note is lower than any later one."
     :forms ((fact (next-note c d))
             (fact (next-note d e))
             (fact (next-note e f))
             (fact (next-note f g))
             (fact (next-note g a))
             (fact (next-note a b))
             (fact (transitive-relation lower-note))
             (rule lower-note-base-rule
               (if (next-note ?x ?y))
               (then (lower-note ?x ?y)))))

    (:id "L088" :title "Length units"
     :why "Units from small to large; chaining and the reverse relation tell the assistant which unit is bigger."
     :forms ((fact (smaller-unit millimeter centimeter))
             (fact (smaller-unit centimeter meter))
             (fact (smaller-unit meter kilometer))
             (fact (transitive-relation smaller-unit))
             (fact (inverse-relation smaller-unit bigger-unit))))

    (:id "L089" :title "Chores"
     :why "Household chores and who has taken which; negation finds the ones nobody has taken."
     :forms ((fact (chore dishes))
             (fact (chore laundry))
             (fact (chore trash))
             (fact (assigned ana dishes))
             (fact (assigned ben laundry))
             (rule chore-assigned-rule
               (if (assigned ?p ?c))
               (then (chore-assigned ?c)))
             (rule unassigned-chore-rule
               (if (chore ?c) (not (chore-assigned ?c)))
               (then (unassigned ?c)))))))

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
    (sibling bob ?who)     ; the questions below get answers as lessons are applied
    (empty-room ?room)
    (ready ?task)
    (overlaps ?a ?b)
    (suggest ?action ?device)
    (alert ?what ?level)
    (clash ?who ?a ?b)
    (overdue ?task)
    (can-help-with ?topic)))

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
    (what-if-retracted kb '(status network down))
    (values)))

(defun what-if-retracted (kb fact)
  "Show what would stop being true if the given FACT were retracted."
  (format t "What if ~a stopped being true?~%" (show fact))
  (cond ((not (known-p kb fact))
         (format t "  (that fact is not in the knowledge base yet)~%"))
        (t
         (let ((gone (retract-fact kb fact)))
           (if (null gone)
               (format t "  (it is derived rather than given, so it cannot be retracted)~%")
               (dolist (old gone)
                 (format t "  would no longer hold: ~a~%" (show old)))))))
  (terpri))

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

(defun split-commas (string)
  (loop with start = 0
        for comma = (position #\, string :start start)
        collect (string-trim " " (subseq string start comma))
        while comma
        do (setf start (1+ comma))))

(defun run-facts ()
  "Print every fact after inference, or only those whose predicate is listed
in the SAI_PREDICATES environment variable (comma separated)."
  (let* ((kb (make-project-kb))
         (wanted (sb-ext:posix-getenv "SAI_PREDICATES"))
         (predicates (and wanted
                          (plusp (length wanted))
                          (mapcar (lambda (name)
                                    (intern (string-upcase name) :symbolic-ai))
                                  (split-commas wanted)))))
    (forward-chain kb)
    (dolist (fact (kb-facts kb))
      (when (or (null predicates) (member (first fact) predicates))
        (format t "~a~%" (show fact))))
    (values)))

(defun main ()
  (let ((mode (or (sb-ext:posix-getenv "SAI_MODE") "demo")))
    (cond ((string= mode "demo") (run-demo))
          ((string= mode "facts") (run-facts))
          ((string= mode "load") nil)
          ((string= mode "validate") (run-validate))
          ((string= mode "evolve") (evolve-step nil))
          ((string= mode "record-failure") (evolve-step t))
          (t (error "Unknown SAI_MODE: ~a" mode)))))

(main)
