/-
Comparator (Lean FRO gold-standard pattern): kernel-checked axiom allowlist per
headline theorem.  Allowed axioms: propext, Classical.choice, Quot.sound.
`#guard_msgs` fails elaboration if the axiom set differs (e.g. sorryAx).
Run: `lake env lean AxiomCheck.lean` (CI comparator job; sandboxed runner).
-/
import BeauvilleLaszlo.Challenge

/--
info: 'BeauvilleLaszlo.beauvilleLaszlo_arithmeticSquare_exact' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BeauvilleLaszlo.beauvilleLaszlo_arithmeticSquare_exact

/--
info: 'BeauvilleLaszlo.beauvilleLaszlo_glueFinFree_exists' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BeauvilleLaszlo.beauvilleLaszlo_glueFinFree_exists

/--
info: 'BeauvilleLaszlo.beauvilleLaszlo_glueFinFree_unique' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms BeauvilleLaszlo.beauvilleLaszlo_glueFinFree_unique
