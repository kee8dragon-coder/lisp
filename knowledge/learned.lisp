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

;; --- L018: Schedule clashes (applied 2026-10-17 17:29 UTC) ---
;; Flags a person who attends two different events in the same time slot.
(rule clash-rule (if (attends ?p ?a) (attends ?p ?b) (scheduled ?a ?t) (scheduled ?b ?t) (different ?a ?b)) (then (clash ?p ?a ?b)))

;; --- L019: Roles and permissions (applied 2026-10-17 17:51 UTC) ---
;; Who holds which role and what each role allows, so the assistant can say who may do what.
(fact (user-role ana admin))
(fact (user-role ben editor))
(fact (user-role cai viewer))
(fact (role-grants admin manage))
(fact (role-grants editor edit))
(fact (role-grants viewer view))
(rule permission-rule (if (user-role ?u ?r) (role-grants ?r ?p)) (then (permitted ?u ?p)))

;; --- L020: Role hierarchy (applied 2026-10-17 18:05 UTC) ---
;; Higher roles inherit everything lower roles are allowed to do.
(fact (role-inherits admin editor))
(fact (role-inherits editor viewer))
(fact (transitive-relation role-inherits))
(rule role-inherits-grants-rule (if (role-inherits ?r ?s) (role-grants ?s ?p)) (then (role-grants ?r ?p)))

;; --- L021: Task dependencies (applied 2026-10-17 18:33 UTC) ---
;; Which tasks depend on which; indirect dependencies and the reverse relation are derived automatically.
(fact (depends-on test build))
(fact (depends-on build compile))
(fact (depends-on deploy test))
(fact (depends-on bundle build))
(fact (transitive-relation depends-on))
(fact (inverse-relation depends-on prerequisite-of))

;; --- L022: Task progress (applied 2026-10-17 19:00 UTC) ---
;; Notes finished work and shows which tasks have a finished prerequisite.
(fact (done compile))
(rule has-done-prerequisite-rule (if (done ?y) (depends-on ?x ?y)) (then (has-done-prerequisite ?x ?y)))

;; --- L023: More family members (applied 2026-10-17 19:21 UTC) ---
;; Gives the family rules more people to work on.
(fact (parent bob ivy))
(fact (parent erin frank))
(fact (parent erin grace))
(fact (parent dave hank))

;; --- L024: Gender facts (applied 2026-10-17 19:43 UTC) ---
;; Records who is female or male so relations can be named precisely.
(fact (female alice))
(fact (female erin))
(fact (female carol))
(fact (female ivy))
(fact (female grace))
(fact (male bob))
(fact (male dave))
(fact (male frank))
(fact (male hank))

;; --- L025: Mother and father (applied 2026-10-17 20:00 UTC) ---
;; A female parent is a mother and a male parent is a father.
(rule mother-rule (if (parent ?p ?c) (female ?p)) (then (mother ?p ?c)))
(rule father-rule (if (parent ?p ?c) (male ?p)) (then (father ?p ?c)))

;; --- L026: Brother and sister (applied 2026-10-17 20:23 UTC) ---
;; A male sibling is a brother and a female sibling is a sister.
(rule brother-rule (if (sibling ?a ?b) (male ?a)) (then (brother ?a ?b)))
(rule sister-rule (if (sibling ?a ?b) (female ?a)) (then (sister ?a ?b)))

;; --- L027: Grandmother and grandfather (applied 2026-10-17 20:48 UTC) ---
;; Grandparents named by gender.
(rule grandmother-rule (if (grandparent ?g ?c) (female ?g)) (then (grandmother ?g ?c)))
(rule grandfather-rule (if (grandparent ?g ?c) (male ?g)) (then (grandfather ?g ?c)))

;; --- L028: Aunt and uncle (applied 2026-10-17 21:08 UTC) ---
;; A female pibling is an aunt and a male pibling is an uncle.
(rule aunt-rule (if (pibling ?a ?c) (female ?a)) (then (aunt ?a ?c)))
(rule uncle-rule (if (pibling ?a ?c) (male ?a)) (then (uncle ?a ?c)))

;; --- L029: Child and descendant (applied 2026-10-17 21:33 UTC) ---
;; The reverse of parent and of ancestor.
(rule child-rule (if (parent ?p ?c)) (then (child ?c ?p)))
(rule descendant-rule (if (ancestor ?a ?d)) (then (descendant ?d ?a)))

;; --- L030: Great-grandparent (applied 2026-10-17 21:56 UTC) ---
;; A parent of a grandparent.
(rule great-grandparent-rule (if (parent ?a ?b) (grandparent ?b ?c)) (then (great-grandparent ?a ?c)))

;; --- L031: Marriage and in-laws (applied 2026-10-17 22:13 UTC) ---
;; Marriage works in both directions; the parent of someone's spouse is a parent-in-law.
(fact (married alice leo))
(fact (married bob nina))
(fact (married dave olga))
(fact (symmetric-relation married))
(rule parent-in-law-rule (if (parent ?p ?a) (married ?a ?b)) (then (parent-in-law ?p ?b)))

;; --- L032: Second parents (applied 2026-10-17 22:38 UTC) ---
;; Adds the other parent for several children.
(fact (parent leo bob))
(fact (parent leo erin))
(fact (parent nina carol))
(fact (parent nina ivy))
(fact (parent olga hank))
(fact (male leo))
(fact (female nina))
(fact (female olga))

;; --- L033: Co-parents (applied 2026-10-17 22:57 UTC) ---
;; Two different people who are parents of the same child.
(rule co-parent-rule (if (parent ?a ?c) (parent ?b ?c) (different ?a ?b)) (then (co-parent ?a ?b)))

;; --- L034: More animals (applied 2026-10-17 23:13 UTC) ---
;; Extends the animal taxonomy with more kinds and a fish and amphibian branch.
(fact (is-a horse mammal))
(fact (is-a bat mammal))
(fact (is-a eagle bird))
(fact (is-a penguin bird))
(fact (is-a fish animal))
(fact (is-a salmon fish))
(fact (is-a shark fish))
(fact (is-a frog amphibian))
(fact (is-a amphibian animal))

;; --- L035: More properties (applied 2026-10-17 23:35 UTC) ---
;; More traits that animals inherit from their categories.
(fact (has fish gills))
(fact (has fish fins))
(fact (has bird wings))
(fact (has mammal milk))
(fact (has amphibian moist-skin))

;; --- L036: Abilities (applied 2026-10-17 23:53 UTC) ---
;; What animals can do; abilities of a category pass down to its members. Flying is listed per animal because not every bird flies.
(fact (can sparrow fly))
(fact (can eagle fly))
(fact (can bat fly))
(fact (can fish swim))
(fact (can penguin swim))
(fact (can bird lay-eggs))
(fact (can mammal nurse-young))
(rule can-inherit-rule (if (is-a ?x ?y) (can ?y ?a)) (then (can ?x ?a)))

;; --- L037: Friendship (applied 2026-10-18 00:07 UTC) ---
;; Friendship works both ways; a friend of a friend is a possible introduction.
(fact (friend-of ana ben))
(fact (friend-of ben cai))
(fact (friend-of cai dee))
(fact (friend-of eli fay))
(fact (symmetric-relation friend-of))
(rule friend-of-friend-rule (if (friend-of ?a ?b) (friend-of ?b ?c) (different ?a ?c)) (then (friend-of-friend ?a ?c)))

;; --- L038: Graph reachability (applied 2026-10-18 00:47 UTC) ---
;; A small network of nodes; works out which nodes can be reached from which.
(fact (edge n1 n2))
(fact (edge n2 n3))
(fact (edge n3 n4))
(fact (edge n1 n5))
(fact (edge n5 n6))
(fact (edge n6 n3))
(rule reach-direct-rule (if (edge ?a ?b)) (then (reachable ?a ?b)))
(rule reach-step-rule (if (edge ?a ?b) (reachable ?b ?c)) (then (reachable ?a ?c)))

;; --- L039: Shared destinations (applied 2026-10-18 01:19 UTC) ---
;; Two different nodes that can both reach the same node.
(rule common-target-rule (if (reachable ?a ?t) (reachable ?b ?t) (different ?a ?b)) (then (shares-target ?a ?b)))

;; --- L040: Successor numbers (applied 2026-10-18 01:49 UTC) ---
;; Counting from 1 to 6 using next facts; less-than is built from them and chained by the generic transitivity rule.
(fact (next 1 2))
(fact (next 2 3))
(fact (next 3 4))
(fact (next 4 5))
(fact (next 5 6))
(fact (transitive-relation less-than))
(rule less-than-base-rule (if (next ?a ?b)) (then (less-than ?a ?b)))

;; --- L041: Greater-than and between (applied 2026-10-18 02:11 UTC) ---
;; The reverse of less-than, plus a between relation for three ordered numbers.
(fact (inverse-relation less-than greater-than))
(rule between-rule (if (less-than ?a ?b) (less-than ?b ?c)) (then (between ?b ?a ?c)))

;; --- L042: Ranking people (applied 2026-10-18 02:40 UTC) ---
;; Height ordering: taller-than chains together and has a shorter-than reverse.
(fact (taller-than ana ben))
(fact (taller-than ben cai))
(fact (taller-than cai dee))
(fact (transitive-relation taller-than))
(fact (inverse-relation taller-than shorter-than))

;; --- L043: Places (applied 2026-10-18 03:05 UTC) ---
;; Where places are, nested from city to country to continent; located-in is chained automatically.
(fact (located-in singapore asia))
(fact (located-in tokyo japan))
(fact (located-in kyoto japan))
(fact (located-in japan asia))
(fact (located-in paris france))
(fact (located-in france europe))
(fact (located-in asia earth))
(fact (located-in europe earth))
(fact (transitive-relation located-in))

;; --- L044: Capitals (applied 2026-10-18 03:32 UTC) ---
;; A capital is a city and is located in its country.
(fact (capital-of tokyo japan))
(fact (capital-of paris france))
(rule capital-located-rule (if (capital-of ?c ?n)) (then (located-in ?c ?n)))
(rule capital-city-rule (if (capital-of ?c ?n)) (then (city ?c)))

;; --- L045: Same country (applied 2026-10-18 04:02 UTC) ---
;; Two different places inside the same country.
(fact (country japan))
(fact (country france))
(rule same-country-rule (if (located-in ?a ?c) (located-in ?b ?c) (country ?c) (different ?a ?b)) (then (same-country ?a ?b)))
