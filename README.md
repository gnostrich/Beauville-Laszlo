# Beauville–Laszlo in Lean 4 / Mathlib

Formalization of the Beauville–Laszlo theorem (affine/module form): gluing `f`-regular
modules over a commutative ring `A` from their localization `A_f`-side and their
`f`-adic-completion `Â`-side along `Â_f`. **This is not flat descent** — `f`-regularity
is load-bearing (`Â ⊗_A Â` is pathological), which is exactly why the theorem exists.

- Headline statements: [`BeauvilleLaszlo/Challenge.lean`](BeauvilleLaszlo/Challenge.lean)
- Precise claims and **what is NOT claimed**: [`STATEMENTS.md`](STATEMENTS.md)
- Campaign log (append-only): [`REGISTRY.md`](REGISTRY.md) / `REGISTRY.jsonl`
- Verdict (one page, all outcomes): `VERDICT.md` (written at close)

Primary prover: [Harmonic Aristotle](https://aristotle.harmonic.fun) (one-round
campaign over a frozen 11-node lemma DAG; driver in `scripts/`).

## Trust protocol

- Mathlib-only imports; pins: Lean `v4.28.0`, Mathlib `v4.28.0`.
- Comparator ([`AxiomCheck.lean`](AxiomCheck.lean)): per-headline-theorem
  `#print axioms` guarded (via `#guard_msgs`) to exactly
  `[propext, Classical.choice, Quot.sound]`; kernel-checked, run sandboxed in CI.
- CI on every push: full `lake build` + comparator + no-`sorry` grep. The comparator
  job is the ship gate and stays red until the campaign completes.

SPDX-License-Identifier: Apache-2.0
