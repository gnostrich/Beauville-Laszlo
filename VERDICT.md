# VERDICT — Beauville–Laszlo formalization

**Outcome: COMPLETE.** All 11 nodes of the frozen lemma DAG are proved and
kernel-checked by Aristotle, and all 3 headline theorems are proved by assembling
those nodes. `BeauvilleLaszlo/Challenge.lean` is a single self-contained library
with **no proof holes** (`sorry`/`admit`/`native_decide` absent). The final
assembled library was re-verified by Aristotle as one unit.

- Toolchain: `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`.
- Acceptance: per-node Lean verification by Aristotle (Harmonic) + the CI ship gate
  (`.github/workflows/ci.yml`): `build` (elaborates) and `comparator` (no-`sorry`
  grep + `AxiomCheck.lean` axiom allowlist).
- Full machine-readable event log: `REGISTRY.jsonl` (append-only).

## Headline theorems (Stage A) — all proved

| Theorem | Content | Proved from nodes |
|---|---|---|
| `beauvilleLaszlo_arithmeticSquare_exact` | Arithmetic square `0 → M → M_f × (M⊗Â) → (M⊗Â)_f → 0` is short exact, for `f`-regular `M` (Stacks 0BNI) | D01 (inj), D04 (exact, via D03+D05), D02 (surj); specialised to `B=Â` via D07, D08 |
| `beauvilleLaszlo_glueFinFree_exists` | Gluing `(A_f)^n` and `Â^n` along `g ∈ GL_n(Â_f)` yields a finite projective `A`-module whose localization is `(A_f)^n` and base change is `Â^n` (Stacks 0BP2, 0BP6) | D12 (finite+projective), D10 (`IsLocalizedModule`), D11 (`IsBaseChange`); via D07, D08 |
| `beauvilleLaszlo_glueFinFree_unique` | Uniqueness of the glued module: a compatible `(u,v)` is injective with range exactly `gluedModule` | D13; its short-exactness hypothesis discharged by `beauvilleLaszlo_arithmeticSquare_exact` |

## Per-node campaign record (frozen 11-node DAG)

Attempt policy (frozen): attempt 1 raw; attempt 2 Stacks proof-sketch hints
(`hints/<node>.md`); attempt 3 hand-crafted ≤2-sublemma split. Max 3 attempts/node.

| Node | Theorem | Result | Attempt | Aristotle project |
|---|---|---|---|---|
| D01 | `sqFst_injective` | proved | 1 (raw) | fe39a79a |
| D02 | `sqSnd_surjective` | proved | 2 (hints) | 0a4b520f |
| D03 | `quotSMulTop_baseChange_bijective` | proved | 1 (raw) | 565784a2 |
| D04 | `sq_exact_of_smulRegular_baseChange` | proved | 1 (raw) | 0f699faf |
| D05 | `isSMulRegular_baseChange` | proved | 2 (hints) | 49b93bca |
| D07 | `isCompletionLike_adicCompletion` | proved | 2 (hints) | 0dba6526 |
| D08 | `isSMulRegular_adicCompletion` | proved | 1 (raw) | c0a72d87 |
| D10 | `gluedFst_isLocalizedModule` | proved | 1 (raw) | 2ecb74db |
| D11 | `gluedSnd_isBaseChange` | proved | 2 (hints) | 2b7a5190 |
| D12 | `gluedModule_finite_projective` | proved | 3 (split) | 763263d8 |
| D13 | `glued_unique` | proved | 2 (hints) | ca0dcb18 |
| — | headline assembly (3 theorems) | proved | 1 | 1b9a2f03 |

Calibration H0 (`calibration_localization_injective`) passed before the wave
(project a33a16ab, clean axioms). Node numbering gaps (D06, D09) are by design: the
frozen DAG is exactly these 11 nodes.

Result quality by attempt: **5/11 on the first raw pass** (D01, D03, D04, D08, D10);
**+5 with Stacks hints** (D02, D05, D07, D11, D13); **D12 on the sublemma split**.
D12 attempt-2 produced a 914-line proof complete except a single hole in a private
matrix-identity lemma (`image_sub_eq`); attempt 3 handed that scaffold back with a
hand-verified derivation of exactly that identity, which closed it.

## Axiom status

Each headline theorem's axiom set is kernel-checked against the allowlist
`[propext, Classical.choice, Quot.sound]` in `AxiomCheck.lean`
(`#print axioms` + `#guard_msgs`), enforced by the CI `comparator` job. Aristotle's
per-node kernel checks reported the same clean set (no `sorryAx`). No node introduced
an axiom outside the allowlist.

## What is NOT claimed (see STATEMENTS.md for the full list)

1. **No fpqc/flat descent.** `f`-regularity is load-bearing; the theorems are false
   without it. `Â ⊗_A Â` is never formed.
2. **No category equivalence (Stage B not shipped).** We prove objects-level gluing
   (existence + uniqueness for finite-free gluing data) and the exact arithmetic
   square — not the full equivalence `A`-Mod ≃ Glue(A_f, Â) of Stacks 0BP2.
3. **`M̂` means `M ⊗_A Â`**, not the adic completion of `M`.
4. **Vector-bundle case is finite-free-pieces only** (rank `n` both sides, one
   transition matrix `g`); glued output is finite projective. General finite
   projective pieces are Zariski-locally of this form, but that reduction is not
   formalized.
5. **Decision D1 not taken:** no Noetherian hypothesis anywhere; the completion
   instantiation is carried by D07/D08 as in the non-Noetherian Stacks treatment.
6. Exactness is `A`-linear on underlying additive groups; the `A_f`/`Â`/`Â_f`
   module structures on outer terms are carried by `IsLocalizedModule` / `IsBaseChange`
   where claimed, and not otherwise.

## Provenance / integrity notes

- The shared preamble initially did not typecheck (`sqSnd` composed a
  Localization-linear map with an `A`-linear projection); repaired via
  `.restrictScalars A` (Aristotle project 790863b7) before the wave.
- Two collector-harness bugs were found and corrected mid-run (both recorded in
  `REGISTRY.jsonl` as superseding findings, not silent edits): `get_files` requires a
  file destination (not a directory); the proved/failed check must strip comments
  before scanning for `sorry` (every node header comment contains the word). One
  transient rate-limit (429) falsely marked D11 as failed and was likewise corrected.
- The assembled library merged 11 node proofs with zero declaration-name collisions
  across 133 declarations.
