;;;; Appended to by the automation, one lesson per run.
;;;; Review changes on the autoevolve branch before merging.

;; --- L001: Sibling relation (applied 2026-10-16 10:03 UTC) ---
;; Two different people with the same parent are siblings; uses the built-in DIFFERENT test.
(rule sibling-rule (if (parent ?p ?a) (parent ?p ?b) (different ?a ?b)) (then (sibling ?a ?b)))

;; --- L002: Grandchild relation (applied 2026-10-16 10:32 UTC) ---
;; The inverse of grandparent.
(rule grandchild-rule (if (grandparent ?x ?y)) (then (grandchild ?y ?x)))

;; --- L003: Aunt or uncle (pibling) (applied 2026-10-16 10:32 UTC) ---
;; A sibling of someone's parent. Depends on the sibling rule from L001.
(rule pibling-rule (if (sibling ?s ?p) (parent ?p ?c)) (then (pibling ?s ?c)))

;; --- L004: Small animal taxonomy (applied 2026-10-16 10:33 UTC) ---
;; Adds is-a facts and makes is-a transitive.
(fact (is-a dog mammal))
(fact (is-a cat mammal))
(fact (is-a mammal animal))
(fact (is-a sparrow bird))
(fact (is-a bird animal))
(rule is-a-transitive (if (is-a ?x ?y) (is-a ?y ?z)) (then (is-a ?x ?z)))
