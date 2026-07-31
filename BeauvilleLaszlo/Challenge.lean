/-
Beauville–Laszlo (affine/module form) — statement layer.

References:
* A. Beauville, Y. Laszlo, "Un lemme de descente", C. R. Acad. Sci. Paris 320 (1995) 335–340.
* Stacks Project, Tag 0BNI ("The Beauville-Laszlo theorem", More on Algebra).

SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# The Beauville–Laszlo theorem (affine/module form)

Let `A` be a commutative ring and `f : A` a non-zerodivisor.  Write `Â` for the `f`-adic
completion of `A`.  The Beauville–Laszlo theorem glues `f`-regular modules over `A` from
their localization away from `f` and their base change to `Â`.  This is *not* flat
descent: `Â ⊗_A Â` is pathological, and `f`-regularity is load-bearing throughout.

Following the Stacks project (Tag 0BNI), the theory is developed for an abstract
"completion-like" `A`-algebra `B` — one for which `A/f^n → B/f^nB` is bijective for all
`n ≥ 1` — and the `f`-adic completion is treated as an instance.  Throughout, the base
change of `M` is `M ⊗[A] B` (NOT the `f`-adic completion of `M`; the two agree for finite
modules over Noetherian rings, and `M ⊗[A] B` is the correct object in general).

Headline statements (Stage A; proofs are the object of the Aristotle campaign):
* `beauvilleLaszlo_arithmeticSquare_exact` — the short exact "arithmetic square"
  `0 → M → M_f × (M ⊗ Â) → (M ⊗ Â)_f → 0` for `f`-regular `M`.
* `beauvilleLaszlo_glueFinFree_exists` — gluing a finite free module over `A_f` and a
  finite free module over `Â` along `g ∈ GL_n(Â_f)` yields a finite projective `A`-module
  with prescribed localization and base change (the vector-bundle case).
* `beauvilleLaszlo_glueFinFree_unique` — uniqueness of the glued module.
-/

open scoped TensorProduct

namespace BeauvilleLaszlo

universe u

-- PREAMBLE START

/-- `B` is a "completion-like" `A`-algebra with respect to `f : A`: reduction mod `f^n`
induces an isomorphism `A/f^n ≅ B/f^nB` for every `n ≥ 1` (stated as: the composite
`A → B/f^nB` is surjective with kernel `(f^n)`).  This is the standing hypothesis of
Stacks Tag 0BNI; the `f`-adic completion `AdicCompletion (Ideal.span {f}) A` satisfies it
(Stacks Tag 0BNJ). -/
structure IsCompletionLike (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B] : Prop where
  surjective_mod : ∀ n : ℕ, 0 < n →
    Function.Surjective (algebraMap A (B ⧸ (Ideal.span {f ^ n}).map (algebraMap A B)))
  ker_mod : ∀ n : ℕ, 0 < n →
    RingHom.ker (algebraMap A (B ⧸ (Ideal.span {f ^ n}).map (algebraMap A B))) =
      Ideal.span {f ^ n}

/-- The base-change map `x ↦ x ⊗ 1 : M →ₗ[A] M ⊗[A] B`. -/
noncomputable def toTensor (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] : M →ₗ[A] M ⊗[A] B :=
  (TensorProduct.mk A M B).flip 1

/-- First map of the Beauville–Laszlo square: `x ↦ (x/1, x ⊗ 1)`. -/
noncomputable def sqFst (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] :
    M →ₗ[A] LocalizedModule (Submonoid.powers f) M × (M ⊗[A] B) :=
  (LocalizedModule.mkLinearMap (Submonoid.powers f) M).prod (toTensor A B M)

/-- Second map of the Beauville–Laszlo square:
`(u, v) ↦ (image of u in (M ⊗ B)_f) - (v/1)`. -/
noncomputable def sqSnd (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] :
    LocalizedModule (Submonoid.powers f) M × (M ⊗[A] B) →ₗ[A]
      LocalizedModule (Submonoid.powers f) (M ⊗[A] B) :=
  (LocalizedModule.map (Submonoid.powers f) (toTensor A B M)).comp
      (LinearMap.fst A (LocalizedModule (Submonoid.powers f) M) (M ⊗[A] B)) -
    (LocalizedModule.mkLinearMap (Submonoid.powers f) (M ⊗[A] B)).comp
      (LinearMap.snd A (LocalizedModule (Submonoid.powers f) M) (M ⊗[A] B))

/-- The gluing defect map for a rank-`n` gluing datum `g` over `Bf` ("`Â_f`"):
`(x, y) ↦ g (ρ ∘ x) - (algebraMap B Bf) ∘ y`, an `A`-linear map
`(Fin n → Rf) × (Fin n → B) →ₗ[A] (Fin n → Bf)`.  Its kernel is the glued module.
Here `ρ : Rf →ₐ[A] Bf` is (necessarily) the canonical map `A_f → Â_f`: any `A`-algebra
map `Rf → Bf` out of the localization is the canonical one. -/
noncomputable def glueDelta (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    (Fin n → Rf) × (Fin n → B) →ₗ[A] (Fin n → Bf) :=
  ((g.toLinearMap.restrictScalars A).comp (ρ.toLinearMap.compLeft (Fin n))).comp
      (LinearMap.fst A (Fin n → Rf) (Fin n → B)) -
    (((IsScalarTower.toAlgHom A B Bf).toLinearMap.compLeft (Fin n)).comp
      (LinearMap.snd A (Fin n → Rf) (Fin n → B)))

/-- The glued module of a rank-`n` gluing datum: the fiber product
`(Fin n → Rf) ×_{(Fin n → Bf)} (Fin n → B)`, as a submodule of the product. -/
noncomputable def gluedModule (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    Submodule A ((Fin n → Rf) × (Fin n → B)) :=
  LinearMap.ker (glueDelta A B Rf Bf ρ n g)

/-- First projection of the glued module, to the `Rf`-side free module. -/
noncomputable def gluedFst (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    ↥(gluedModule A B Rf Bf ρ n g) →ₗ[A] (Fin n → Rf) :=
  (LinearMap.fst A (Fin n → Rf) (Fin n → B)).comp (gluedModule A B Rf Bf ρ n g).subtype

/-- Second projection of the glued module, to the `B`-side free module. -/
noncomputable def gluedSnd (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    ↥(gluedModule A B Rf Bf ρ n g) →ₗ[A] (Fin n → B) :=
  (LinearMap.snd A (Fin n → Rf) (Fin n → B)).comp (gluedModule A B Rf Bf ρ n g).subtype

-- PREAMBLE END

/-! ## Headline theorems (Stage A) -/

/-- **Beauville–Laszlo arithmetic square** (Stage A1).
For a commutative ring `A`, a non-zerodivisor `f`, and an `A`-module `M` on which `f` is
regular, the square
`0 → M → M_f × (M ⊗[A] Â) → (M ⊗[A] Â)_f → 0`
is a short exact sequence, where `Â = AdicCompletion (Ideal.span {f}) A`.
(Stacks Tag 0BNI; the case `M = A` is the definition of a glueing pair.) -/
theorem beauvilleLaszlo_arithmeticSquare_exact
    (A : Type u) [CommRing A] (f : A) (hA : IsSMulRegular A f)
    (M : Type u) [AddCommGroup M] [Module A M] (hM : IsSMulRegular M f) :
    Function.Injective (sqFst A f (AdicCompletion (Ideal.span {f}) A) M) ∧
      Function.Exact (sqFst A f (AdicCompletion (Ideal.span {f}) A) M)
        (sqSnd A f (AdicCompletion (Ideal.span {f}) A) M) ∧
      Function.Surjective (sqSnd A f (AdicCompletion (Ideal.span {f}) A) M) := by
  sorry

/-- **Beauville–Laszlo gluing, existence** (Stage A2, vector-bundle case).
Gluing the finite free modules `(A_f)^n` and `Â^n` along a gluing datum
`g ∈ GL_n(Â_f)` produces a finite projective `A`-module — the fiber product
`gluedModule` — whose localization at `f` is `(A_f)^n` (via `IsLocalizedModule`) and
whose base change to `Â` is `Â^n` (via `IsBaseChange`).
(Stacks Tags 0BP2 and 0BP6.) -/
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
        (gluedSnd A (AdicCompletion (Ideal.span {f}) A) Rf Bf ρ n g) := by
  sorry

/-- **Beauville–Laszlo gluing, uniqueness** (Stage A2, vector-bundle case).
Any `f`-regular `A`-module `N` equipped with maps to the pieces of a rank-`n` gluing
datum that (a) exhibit `(Fin n → Rf)` as the localization of `N` at `f`, (b) exhibit
`(Fin n → Â)` as the base change of `N` to `Â`, and (c) are compatible with the gluing
datum `g`, is canonically isomorphic to the glued module: `N → gluedModule` induced by
`(u, v)` is injective with image exactly `gluedModule`. -/
theorem beauvilleLaszlo_glueFinFree_unique
    (A : Type u) [CommRing A] (f : A) (hA : IsSMulRegular A f)
    (Rf : Type u) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf]
    [Algebra (AdicCompletion (Ideal.span {f}) A) Bf]
    [IsScalarTower A (AdicCompletion (Ideal.span {f}) A) Bf]
    [IsLocalization.Away (algebraMap A (AdicCompletion (Ideal.span {f}) A) f) Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf))
    (N : Type u) [AddCommGroup N] [Module A N] (hN : IsSMulRegular N f)
    (u : N →ₗ[A] (Fin n → Rf)) (hu : IsLocalizedModule (Submonoid.powers f) u)
    (v : N →ₗ[A] (Fin n → AdicCompletion (Ideal.span {f}) A))
    (hv : IsBaseChange (AdicCompletion (Ideal.span {f}) A) v)
    (hcompat :
      (glueDelta A (AdicCompletion (Ideal.span {f}) A) Rf Bf ρ n g).comp (u.prod v) = 0) :
    Function.Injective (u.prod v) ∧
      Set.range (u.prod v) =
        ↑(gluedModule A (AdicCompletion (Ideal.span {f}) A) Rf Bf ρ n g) := by
  sorry

end BeauvilleLaszlo
