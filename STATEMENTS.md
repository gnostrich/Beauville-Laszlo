# Beauville–Laszlo: what is stated, and what is NOT claimed

Sources of truth for hypotheses: Beauville–Laszlo, *Un lemme de descente*, CRAS 320
(1995) 335–340; Stacks Project Tag [0BNI](https://stacks.math.columbia.edu/tag/0BNI)
(the "Beauville-Laszlo theorem" section of More on Algebra), whose non-Noetherian
treatment we follow. Equivalence theorem: Tag 0BP2; finite projective descent: Tag 0BP6.

## Conventions

- `A` commutative ring, `f : A`. "`f`-regular on `X`" is `IsSMulRegular X f`
  (multiplication by `f` injective).
- `Â := AdicCompletion (Ideal.span {f}) A` (Mathlib's `f`-adic completion, with its
  Mathlib `CommRing`/`Algebra A` structure).
- **`M̂` means `M ⊗[A] Â`**, NOT the `f`-adic completion of `M`. The two agree for
  finite modules over Noetherian rings; `M ⊗[A] Â` is the object for which the theorem
  holds in general (Stacks convention).
- `M_f := LocalizedModule (Submonoid.powers f) M`. Exactness statements are about
  underlying `A`-modules (exactness is scalar-blind).
- Abstract layer: `IsCompletionLike A f B` packages the Stacks standing hypothesis
  "`A/f^n → B/f^nB` bijective for all `n ≥ 1`" (as surjectivity + kernel of
  `algebraMap A (B ⧸ (span {f^n}).map (algebraMap A B))`). The completion instance is
  Stacks 0BNJ (= node D07).
- Stage A2 gluing data are matrix-style: `g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)` with
  `Bf` any `IsLocalization.Away`-model of `Â_f` — i.e. `g ∈ GL_n(Â_f)`, the
  vector-bundle transition matrix. `ρ : Rf →ₐ[A] Bf` is quantified as data; any
  `A`-algebra map out of the localization `Rf = A_f` is automatically the canonical one,
  so this loses no strength.
- All statements are single-universe (`Type u`).

## Headline theorems (verbatim from `BeauvilleLaszlo/Challenge.lean`)

### Stage A1 — the arithmetic square

```lean
theorem beauvilleLaszlo_arithmeticSquare_exact
    (A : Type u) [CommRing A] (f : A) (hA : IsSMulRegular A f)
    (M : Type u) [AddCommGroup M] [Module A M] (hM : IsSMulRegular M f) :
    Function.Injective (sqFst A f (AdicCompletion (Ideal.span {f}) A) M) ∧
      Function.Exact (sqFst A f (AdicCompletion (Ideal.span {f}) A) M)
        (sqSnd A f (AdicCompletion (Ideal.span {f}) A) M) ∧
      Function.Surjective (sqSnd A f (AdicCompletion (Ideal.span {f}) A) M)
```

where `sqFst = x ↦ (x/1, x ⊗ 1)` and `sqSnd = (u, v) ↦ (loc. image of u) - v/1`, i.e.
exactness of `0 → M → M_f × (M ⊗ Â) → (M ⊗ Â)_f → 0` for `f`-regular `M`.

### Stage A2 — vector-bundle gluing (existence)

```lean
theorem beauvilleLaszlo_glueFinFree_exists
    (A : Type u) [CommRing A] (f : A) (hA : IsSMulRegular A f)
    (Rf : Type u) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf]
    [Algebra (AdicCompletion (Ideal.span {f}) A) Bf]
    [IsScalarTower A (AdicCompletion (Ideal.span {f}) A) Bf]
    [IsLocalization.Away (algebraMap A (AdicCompletion (Ideal.span {f}) A) f) Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    Module.Finite A ↥(gluedModule A (AdicCompletion (Ideal.span {f}) A) Rf Bf ρ n g) ∧
      Module.Projective A ↥(gluedModule A (AdicCompletion (Ideal.span {f}) A) Rf Bf ρ n g) ∧
      IsLocalizedModule (Submonoid.powers f)
        (gluedFst A (AdicCompletion (Ideal.span {f}) A) Rf Bf ρ n g) ∧
      IsBaseChange (AdicCompletion (Ideal.span {f}) A)
        (gluedSnd A (AdicCompletion (Ideal.span {f}) A) Rf Bf ρ n g)
```

`gluedModule` is the fiber product `ker((x, y) ↦ g(ρ ∘ x) - y)` inside
`(Fin n → Rf) × (Fin n → Â)`.

### Stage A2 — vector-bundle gluing (uniqueness)

```lean
theorem beauvilleLaszlo_glueFinFree_unique
    ( … same setup … )
    (N : Type u) [AddCommGroup N] [Module A N] (hN : IsSMulRegular N f)
    (u : N →ₗ[A] (Fin n → Rf)) (hu : IsLocalizedModule (Submonoid.powers f) u)
    (v : N →ₗ[A] (Fin n → AdicCompletion (Ideal.span {f}) A))
    (hv : IsBaseChange (AdicCompletion (Ideal.span {f}) A) v)
    (hcompat : (glueDelta …).comp (u.prod v) = 0) :
    Function.Injective (u.prod v) ∧ Set.range (u.prod v) = ↑(gluedModule …)
```

## Frozen lemma DAG (11 nodes; assembly is glue, not a node)

| node | statement | depends on (as hypothesis args) |
|------|-----------|-------------------------------|
| D01 | `sqFst` injective for `f`-regular `M` | — |
| D02 | `sqSnd` surjective, any `M` | — |
| D03 | `M/f^nM ≅ (M⊗B)/f^n(M⊗B)` via base change | — |
| D04 | middle exactness given `f`-regular `M ⊗ B` | D03 |
| D05 | `f`-regular `M` ⟹ `f`-regular `M ⊗ B` (deep BL input) | — |
| D07 | `Â` is completion-like (Stacks 0BNJ) | — |
| D08 | `f` nzd on `A` ⟹ `f` nzd on `Â` | — |
| D10 | `gluedFst` is `IsLocalizedModule` | — |
| D11 | `gluedSnd` is `IsBaseChange` | — |
| D12 | glued module finite projective (existence crux) | — |
| D13 | uniqueness via abstract A1 | D01–D05 (assembled) |

Assembly: A1-headline = D01∧D04(D03)∧D05∧D02 at `B := Â` via D07, D08.
A2-headlines = D10–D13 at `B := Â` via D07, D08.

## What we do NOT claim

1. **Not flat/fpqc descent.** No claim that `A → A_f × Â` is a flat cover with descent
   datum in the fpqc sense; `Â ⊗_A Â` is pathological in general and the proof never
   forms it. `f`-regularity is essential and load-bearing; the theorems are false
   without it.
2. **No category equivalence (Stage B unshipped unless stated otherwise in
   VERDICT.md).** We claim objects-level gluing (existence + uniqueness for finite free
   gluing data) and the exact arithmetic square — not the full equivalence
   `f`-regular/glueable `A`-Mod ≃ Glue(A_f, Â) of Stacks 0BP2.
3. **`M̂` is `M ⊗_A Â`**, not the adic completion of `M`; no claim about
   `AdicCompletion (span {f}) M` for infinite modules.
4. **Vector-bundle case is free-pieces-only.** Stage A2 glues *finite free* pieces
   (rank `n` both sides, one transition matrix `g`); glued output is finite
   *projective*. No claim for general finite projective pieces (they are Zariski-locally
   of this form, but that reduction is not formalized).
5. **Decision D1: not taken.** No Noetherian hypothesis anywhere; the completion
   instantiation is carried by nodes D07/D08 exactly as in the non-Noetherian Stacks
   treatment. If D07/D08 fail in the campaign, the abstract (`IsCompletionLike`) layer
   stands on its own and the gap will be recorded in VERDICT.md — the fallback is a
   generality gap in the *instance*, never a silent weakening of the headline.
6. Exactness claims are `A`-linear (underlying additive groups); module structures over
   `A_f`, `Â`, `Â_f` on the outer terms are carried by the canonical Mathlib predicates
   (`IsLocalizedModule`, `IsBaseChange`) where claimed, and not otherwise.
