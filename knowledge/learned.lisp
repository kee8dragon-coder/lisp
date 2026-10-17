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

;; --- L005: Property inheritance (applied 2026-10-16 10:52 UTC) ---
;; Things inherit properties from the categories they belong to.
(fact (has animal cells))
(fact (has mammal fur))
(fact (has bird feathers))
(rule inherit-property (if (is-a ?x ?y) (has ?y ?p)) (then (has ?x ?p)))

;; --- L006: Cousin relation (applied 2026-10-17 10:11 UTC) ---
;; Children of two siblings are cousins.
(rule cousin-rule (if (parent ?p1 ?a) (parent ?p2 ?b) (sibling ?p1 ?p2)) (then (cousin ?a ?b)))

;; --- L007: Generic transitivity (applied 2026-10-17 13:07 UTC) ---
;; Any relation declared with transitive-relation is chained automatically (a to b and b to c gives a to c).
(rule generic-transitive-rule (if (transitive-relation ?r) (?r ?a ?b) (?r ?b ?c)) (then (?r ?a ?c)))

;; --- L008: Generic symmetry (applied 2026-10-17 13:34 UTC) ---
;; Any relation declared with symmetric-relation works in both directions.
(rule generic-symmetric-rule (if (symmetric-relation ?r) (?r ?a ?b)) (then (?r ?b ?a)))

;; --- L009: Generic inverse (applied 2026-10-17 13:58 UTC) ---
;; inverse-relation facts such as (inverse-relation depends-on prerequisite-of) create the reverse relation automatically.
(rule generic-inverse-rule (if (inverse-relation ?r ?s) (?r ?a ?b)) (then (?s ?b ?a)))

;; --- L010: Rooms and devices (applied 2026-10-17 14:20 UTC) ---
;; Starter home model: which devices are in which rooms, and what kind each one is.
(fact (device-in lamp-1 lounge))
(fact (device-in lamp-2 study))
(fact (device-in heater lounge))
(fact (device-in speaker-1 study))
(fact (device-type lamp-1 light))
(fact (device-type lamp-2 light))
(fact (device-type heater climate))
(fact (device-type speaker-1 audio))
(rule room-contains-rule (if (device-in ?d ?r)) (then (room-contains ?r ?d)))

;; --- L011: Device lookups (applied 2026-10-17 14:46 UTC) ---
;; Answers what kinds of device a room has and which lights are in which room.
(rule room-has-type-rule (if (device-in ?d ?r) (device-type ?d ?t)) (then (room-has-type ?r ?t)))
(rule light-in-rule (if (device-in ?d ?r) (device-type ?d light)) (then (light-in ?d ?r)))

;; --- L012: Presence and lights (applied 2026-10-17 15:05 UTC) ---
;; Knows who is in which room and suggests turning on the lights where someone is; explain shows why.
(fact (at ana study))
(fact (at ben lounge))
(rule occupied-rule (if (at ?p ?r)) (then (occupied ?r)))
(rule suggest-light-rule (if (at ?p ?r) (light-in ?d ?r)) (then (suggest turn-on ?d)))

;; --- L013: Preferences (applied 2026-10-17 15:30 UTC) ---
;; Uses what people prefer to suggest playing music for one person and muting the speaker for another.
(fact (prefers ana quiet))
(fact (prefers ben music))
(fact (device-in speaker-2 lounge))
(fact (device-type speaker-2 audio))
(rule suggest-music-rule (if (at ?p ?r) (prefers ?p music) (device-in ?d ?r) (device-type ?d audio)) (then (suggest play-music ?d)))
(rule suggest-mute-rule (if (at ?p ?r) (prefers ?p quiet) (device-in ?d ?r) (device-type ?d audio)) (then (suggest mute ?d)))

;; --- L014: System components (applied 2026-10-17 15:56 UTC) ---
;; Which parts of a system need which other parts; chains are followed using the generic transitivity rule.
(fact (needs cooling power))
(fact (needs compute power))
(fact (needs compute cooling))
(fact (needs network power))
(fact (needs assistant compute))
(fact (needs assistant network))
(fact (transitive-relation needs))

;; --- L015: Status and failures (applied 2026-10-17 16:15 UTC) ---
;; A demo status report: when a component is down, everything that needs it is marked degraded, and explain shows the chain.
(fact (status power ok))
(fact (status cooling ok))
(fact (status compute ok))
(fact (status network down))
(rule failing-rule (if (status ?c down)) (then (failing ?c)))
(rule degraded-rule (if (status ?c down) (needs ?s ?c)) (then (degraded ?s)))

;; --- L016: Alerts (applied 2026-10-17 16:44 UTC) ---
;; Turns failures into critical alerts and degraded systems into warnings.
(rule alert-failing-rule (if (failing ?c)) (then (alert ?c critical)))
(rule alert-degraded-rule (if (degraded ?s)) (then (alert ?s warning)))

;; --- L017: Calendar (applied 2026-10-17 17:06 UTC) ---
;; Events, their time slots, and who attends; works out when each person is busy.
(fact (scheduled standup mon-9))
(fact (scheduled review mon-9))
(fact (scheduled lunch mon-12))
(fact (attends ana standup))
(fact (attends ana review))
(fact (attends ben standup))
(fact (attends ben lunch))
(rule busy-rule (if (attends ?p ?e) (scheduled ?e ?t)) (then (busy ?p ?t)))
