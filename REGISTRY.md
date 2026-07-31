# REGISTRY — Beauville–Laszlo formalization campaign

Append-only log of decisions, runs, and verdicts. Machine log: `REGISTRY.jsonl`.
Commit-before-run discipline: the scaffold, statements, and frozen DAG are committed
before any Aristotle submission.

## Phase 0 — duplication kill-check (2026-07-31) — VERDICT: CLEAR

- Loogle (Mathlib master): 0 declarations containing `Beauville`, `Laszlo`,
  `BeauvilleLaszlo`, `GluingPair`.
- Web/Zulip search: no Lean formalization, no Mathlib PR, no Zulip campaign found for
  "Beauville-Laszlo".
- FLT project (Imperial) blueprint: no Beauville–Laszlo on the roadmap (their route is
  quaternionic, not Bun_G).
- K0 not triggered. Proceed.

## Decision D1 (AdicCompletion API) — NOT TAKEN (2026-07-31)

Mathlib `AdicCompletion` provides `CommRing`, `Algebra A`, `evalₐ`, lift API — enough
to *state* everything with `Â := AdicCompletion (Ideal.span {f}) A` and zero new
infrastructure. The needed universal properties (`A/f^n ≅ Â/f^nÂ`, `f` nzd descends to
`Â`) are NOT assumed: they are proof obligations, isolated as DAG nodes D07/D08.
No Noetherian downgrade at statement level. If D07/D08 fail, the abstract
`IsCompletionLike` layer stands and the instance gap is recorded in VERDICT.md.

## Harness & campaign configuration (frozen before any run)

- Prover: Harmonic Aristotle (API v3, `aristotlelib` 2.1.0), toolchain
  `leanprover/lean4:v4.28.0`, Mathlib `v4.28.0`.
- H0 calibration: `calibration_localization_injective` (localization map injective on
  an `f`-regular module — known short Mathlib proof, same API flavor as the DAG).
  K1: H0 fails ⟹ verdict "harness failure", CLOSED.
- Per-node budget: 3 attempts — (1) raw, (2) + Stacks proof-sketch hints, (3) one
  split into ≤2 sublemmas (children inherit remaining budget; no further splits).
- One statement-repair pass per node allowed, logged.
- **Interpretation note (fixed pre-campaign):** shared-preamble elaboration defects
  surfaced by the H0 file or by the scaffold CI build count as ONE global
  statement-layer repair event (the preamble is common to all nodes), not as per-node
  defects; per-node K2 accounting (>50% ⟹ "Mathlib API wall") applies to node-specific
  statements only.
- Acceptance: Aristotle's server-side Lean verification (kernel-checked on their side),
  per the mission owner's trust directive ("delegate maximally, no local verification").
  The *binding* final gate is CI on GitHub runners: full `lake build` + comparator
  (`AxiomCheck.lean`: per-theorem `#print axioms` guarded to exactly
  `[propext, Classical.choice, Quot.sound]`, plus a no-`sorry` grep). Axiom column in
  the attempt log therefore reads `deferred_to_ci_comparator`.
- Verdict rules (frozen): Stage A fully proved ⟹ SHIPPED-A; Stage B only with leftover
  budget, incomplete Stage B is not a failure; Stage A incomplete ⟹ distinguish genuine
  prover failure vs statement-layer defect; terminal verdict "inconclusive at this
  scale with this method" is binding and CLOSED.

## Branch note

Mission text names branch `claude/beauville-laszlo-v0`; the session's designated
branch is `claude/beauville-laszlo-lean4-ql069v` (system git requirement — only this
branch may be pushed). All work lives on `claude/beauville-laszlo-lean4-ql069v`.

## Attempt log

See `REGISTRY.jsonl` (one line per attempt: node_id, attempt, config, result,
wall_time, axioms, lines).
