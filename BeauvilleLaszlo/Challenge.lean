/-
Beauville–Laszlo formalization — self-contained verified library.

Contents (in order): a shared preamble of definitions; the eleven DAG-node lemmas
of the frozen lemma graph, each proved and kernel-checked; and the three headline
theorems, each proved by specialising those lemmas to
`B := AdicCompletion (Ideal.span {f}) A`.

Every proof in this file is complete: it contains no proof holes, no added axioms,
and no `native_decide`.  Each headline theorem's axiom set is kernel-checked against
the allowlist [propext, Classical.choice, Quot.sound] by `AxiomCheck.lean`.

References: Beauville–Laszlo, *Un lemme de descente*, CRAS 320 (1995); Stacks Project
Tags 0BNI, 0BNJ, 0BP2, 0BP6.  See STATEMENTS.md for the precise not-claimed list and
VERDICT.md for the campaign record.
-/
import Mathlib

open scoped TensorProduct

namespace BeauvilleLaszlo

universe u

/- ===================== shared preamble ===================== -/
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
  ((LocalizedModule.map (Submonoid.powers f) (toTensor A B M)).restrictScalars A).comp
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
/- ===================== verified node lemmas ===================== -/
/- ===== node D01 (D01_a1): verified by Aristotle ===== -/
/-- Left exactness of the Beauville-Laszlo square: for `f`-regular `M`, the map
`M → M_f × (M ⊗ B)` is injective (already via the first component). -/
theorem sqFst_injective
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] (hM : IsSMulRegular M f) :
    Function.Injective (sqFst A f B M) := by
  have hloc : Function.Injective
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) := by
    rw [← LinearMap.ker_eq_bot]
    ext m
    constructor
    · intro hm
      rw [LocalizedModule.mem_ker_mkLinearMap_iff] at hm
      obtain ⟨r, ⟨n, hn⟩, hr⟩ := hm
      subst r
      have hm0 : m = 0 := (hM.pow n) (by simpa using hr)
      exact hm0
    · intro hm
      rw [Submodule.mem_bot] at hm
      subst m
      simp
  intro x y hxy
  apply hloc
  exact congrArg Prod.fst hxy
/- ===== node D02 (D02_a2): verified by Aristotle ===== -/
/-- Additivity of `LocalizedModule.mk` in the numerator. -/
private lemma bl_mk_add {A : Type u} [CommRing A] {S : Submonoid A}
    {N : Type u} [AddCommGroup N] [Module A N] (a b : N) (s : S) :
    LocalizedModule.mk (a + b) s = LocalizedModule.mk a s + LocalizedModule.mk b s :=
  (OreLocalization.add_oreDiv ..).symm

/-- Elements of the form `w/1` are in the image of `sqSnd`. -/
private lemma bl_mk_one_mem_range
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] (w : M ⊗[A] B) :
    LocalizedModule.mk w 1 ∈ LinearMap.range (sqSnd A f B M) := by
  refine ⟨(0, -w), ?_⟩
  simp only [sqSnd, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, map_zero, LocalizedModule.mkLinearMap_apply, map_neg, zero_sub, neg_neg]

/-- Elements of the form `(x ⊗ 1)/s` are in the image of `sqSnd`. -/
private lemma bl_mk_tmul_one_mem_range
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] (x : M) (s : Submonoid.powers f) :
    LocalizedModule.mk (toTensor A B M x) s ∈ LinearMap.range (sqSnd A f B M) := by
  refine ⟨(LocalizedModule.mk x s, 0), ?_⟩
  simp only [sqSnd, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, LinearMap.restrictScalars_apply, map_zero, sub_zero,
    LocalizedModule.map_mk]

/-- Surjectivity of `A → B/f^nB` in elementwise form. -/
private lemma bl_decomp
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B) (n : ℕ) (hn : 0 < n) (b : B) :
    ∃ (a : A) (c : B), b = algebraMap A B a + algebraMap A B (f ^ n) * c := by
  have hsurj := hB.surjective_mod n hn
  obtain ⟨a, ha⟩ := hsurj b
  have ha' : Ideal.Quotient.mk (Ideal.map (algebraMap A B) (Ideal.span {f ^ n})) (algebraMap A B a) =
             Ideal.Quotient.mk (Ideal.map (algebraMap A B) (Ideal.span {f ^ n})) b := by
    simp [← ha]
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ha'
  rw [Ideal.map_span] at ha'
  have : algebraMap A B '' {f ^ n} = {algebraMap A B (f ^ n)} := by simp
  rw [this] at ha'
  rw [Ideal.mem_span_singleton] at ha'
  obtain ⟨c, hc⟩ := ha'
  use a, -c
  linear_combination -hc

/-- Splitting a pure tensor along a decomposition `b = a + f^n c`. -/
private lemma bl_tmul_split
    (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] (x : M) (a : A) (r : A) (c : B) :
    x ⊗ₜ[A] (algebraMap A B a + algebraMap A B r * c)
      = a • (toTensor A B M x) + r • (x ⊗ₜ[A] c) := by
  simp [toTensor]
  rw [TensorProduct.tmul_add]
  congr 1 <;>
  · rw [Algebra.algebraMap_eq_smul_one]
    simp [mul_comm]

/-- Every element `w/f^n` with `n > 0` is in the image of `sqSnd`. -/
private lemma bl_mk_pow_mem_range
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (M : Type u) [AddCommGroup M] [Module A M]
    (n : ℕ) (hn : 0 < n) (w : M ⊗[A] B) :
    LocalizedModule.mk w (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) ∈
      LinearMap.range (sqSnd A f B M) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul x b =>
      obtain ⟨a, c, hac⟩ := bl_decomp A f B hB n hn b
      rw [hac, bl_tmul_split A B M x a (f ^ n) c, bl_mk_add]
      refine Submodule.add_mem _ ?_ ?_
      · rw [← LocalizedModule.smul'_mk]
        exact Submodule.smul_mem _ _ (bl_mk_tmul_one_mem_range A f B M x _)
      · have h2 : LocalizedModule.mk ((f ^ n) • (x ⊗ₜ[A] c))
            (⟨f ^ n, n, rfl⟩ : Submonoid.powers f)
            = LocalizedModule.mk (x ⊗ₜ[A] c) 1 :=
          LocalizedModule.mk_cancel (⟨f ^ n, n, rfl⟩ : Submonoid.powers f) _
        rw [h2]
        exact bl_mk_one_mem_range A f B M _
  | add w₁ w₂ h₁ h₂ => rw [bl_mk_add]; exact Submodule.add_mem _ h₁ h₂

/-- Right exactness of the Beauville-Laszlo square holds for every module `M`
(Stacks 0BNI: uses only surjectivity of `A → B/f^nB`). -/
theorem sqSnd_surjective
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (M : Type u) [AddCommGroup M] [Module A M] :
    Function.Surjective (sqSnd A f B M) := by
  intro t
  induction t using LocalizedModule.induction_on with
  | _ w s =>
    obtain ⟨k, hk⟩ := s.2
    have hfs : (⟨f ^ (k + 1), k + 1, rfl⟩ : Submonoid.powers f)
        = (⟨f, 1, pow_one f⟩ : Submonoid.powers f) * s := by
      apply Subtype.ext
      simp [← hk, pow_succ']
    have hmk : LocalizedModule.mk w s
        = LocalizedModule.mk (f • w) (⟨f ^ (k + 1), k + 1, rfl⟩ : Submonoid.powers f) := by
      rw [hfs]
      exact (LocalizedModule.mk_cancel_common_left (⟨f, 1, pow_one f⟩ : Submonoid.powers f) s w).symm
    rw [hmk]
    exact bl_mk_pow_mem_range A f B hB M (k + 1) (Nat.succ_pos k) (f • w)
/- ===== node D03 (D03_a1): verified by Aristotle ===== -/
private theorem tensorMk_bijective_of_surjective
    (A : Type u) [CommRing A]
    (C : Type u) [CommRing C] [Algebra A C]
    (hsurj : Function.Surjective (algebraMap A C))
    (M : Type u) [AddCommGroup M] [Module A M] :
    Function.Surjective ((TensorProduct.mk A C M) 1) ∧
      LinearMap.ker ((TensorProduct.mk A C M) 1) =
        RingHom.ker (algebraMap A C) • (⊤ : Submodule A M) := by
  -- The map (TensorProduct.mk A C M) 1 : M →ₗ[A] C ⊗[A] M sends m ↦ 1 ⊗ m
  -- For surjectivity: any c ⊗ m = (algebraMap a) ⊗ m = a • (1 ⊗ m) = 1 ⊗ (a • m)
  -- For kernel: 1 ⊗ m = 0 iff m is in ker(algebraMap) • M
  refine ⟨?_, ?_⟩
  · -- Surjectivity: any c ⊗ m = (algebraMap a) ⊗ m = 1 ⊗ (a • m) for some a
    intro x
    induction x using TensorProduct.induction_on with
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [← ha, ← hb, map_add]⟩
    | tmul c m =>
      obtain ⟨a, rfl⟩ := hsurj c
      use a • m
      simp only [TensorProduct.mk_apply]
      rw [TensorProduct.tmul_smul]
      have : a • (1 : C) = algebraMap A C a := by rw [Algebra.smul_def, mul_one]
      exact congrArg (· ⊗ₜ[A] m) this
    | zero => exact ⟨0, by simp⟩
  · -- Kernel: 1 ⊗ m = 0 iff m ∈ ker • M
    set I := RingHom.ker (algebraMap A C) with hI
    apply le_antisymm
    · -- 1 ⊗ m = 0 → m ∈ I • M
      -- Use bilinear map to quotient: C × M → M/I•M
      -- For 1 ⊗ m = 0, applying this bilinear map gives m ∈ I•M
      set Q := M ⧸ I • (⊤ : Submodule A M)
      set π : M →ₗ[A] Q := (I • (⊤ : Submodule A M)).mkQ
      -- Define B : C × M → Q by B(c, n) = π(a • n) where a lifts c
      -- Well-defined: if c = 0, choose a ∈ I, then a • n ∈ I • M, so π(a • n) = 0
      have hwell : ∀ c : C, ∀ n : M, ∀ a₁ a₂ : A, algebraMap A C a₁ = c → algebraMap A C a₂ = c →
          π (a₁ • n) = π (a₂ • n) := by
        intro c n a₁ a₂ h₁ h₂
        have hmem : a₁ - a₂ ∈ I := by rw [hI]; exact RingHom.mem_ker.mpr (by simp [h₁, h₂])
        have hsub : a₁ • n - a₂ • n = (a₁ - a₂) • n := (sub_smul a₁ a₂ n).symm
        simp only [π]
        have hlin : ∀ x y : M, (I • (⊤ : Submodule A M)).mkQ (x - y) = (I • (⊤ : Submodule A M)).mkQ x - (I • (⊤ : Submodule A M)).mkQ y := by
          intro x y; apply LinearMap.map_sub
        rw [eq_comm, ← sub_eq_zero, ← hlin (a₂ • n) (a₁ • n)]
        rw [show a₂ • n - a₁ • n = -((a₁ - a₂) • n) by rw [sub_smul, neg_sub]]
        rw [map_neg, neg_eq_zero]
        -- (a₁ - a₂) • n ∈ I • M since a₁ - a₂ ∈ I
        -- Need: (I • ⊤).mkQ ((a₁ - a₂) • n) = 0
        -- This is true because (a₁ - a₂) • n ∈ I • ⊤
        have hmem' : (a₁ - a₂) • n ∈ I • (⊤ : Submodule A M) := Submodule.smul_mem_smul hmem (Submodule.mem_top)
        have : (I • (⊤ : Submodule A M)).mkQ ((a₁ - a₂) • n) = 0 := by
          simp only [Submodule.mkQ_apply]
          rw [Submodule.Quotient.mk_eq_zero]
          exact hmem'
        exact this
      -- Define f : C →ₗ[A] M →ₗ[A] Q
      -- First, define for each c: M → Q by n ↦ π((a • n)) where a lifts c
      -- This is linear in n
      -- Then show it's linear in c using hwell
      let B : C →ₗ[A] M →ₗ[A] Q := {
        toFun := fun c => π.comp (LinearMap.lsmul A M (hsurj c).choose)
        map_add' := by
          intro c d
          ext n
          simp only [LinearMap.comp_apply, LinearMap.lsmul_apply, LinearMap.add_apply]
          have hspec : algebraMap A C ((hsurj c).choose + (hsurj d).choose) = c + d := by
            rw [map_add, (hsurj c).choose_spec, (hsurj d).choose_spec]
          calc π ((hsurj (c + d)).choose • n)
              = π (((hsurj c).choose + (hsurj d).choose) • n) := (hwell (c + d) n _ _ hspec (hsurj (c + d)).choose_spec).symm
            _ = π ((hsurj c).choose • n) + π ((hsurj d).choose • n) := by rw [add_smul, map_add]
        map_smul' := by
          intro r c
          ext n
          have hspec : algebraMap A C (r • (hsurj c).choose) = r • c := by
            rw [Algebra.smul_def, map_mul, (hsurj c).choose_spec, Algebra.smul_def]
            congr 1
          calc π ((hsurj (r • c)).choose • n)
              = π ((r • (hsurj c).choose) • n) := (hwell (r • c) n _ _ hspec (hsurj (r • c)).choose_spec).symm
            _ = π (r • ((hsurj c).choose • n)) := by congr 1; exact smul_assoc r (hsurj c).choose n
            _ = r • π ((hsurj c).choose • n) := by rw [map_smul]
      }
      -- Lift B to a linear map on the tensor product
      let φ : C ⊗[A] M →ₗ[A] Q := TensorProduct.lift B
      -- Show that φ(1 ⊗ m) = π(m) for all m
      have hφ_tmul : ∀ m : M, φ (1 ⊗ₜ[A] m) = π m := by
        intro m
        -- B(1) = π because 1 can be lifted to 1 ∈ A
        have hB1 : B 1 = π := by
          ext n
          have hspec : algebraMap A C (Classical.choose (hsurj 1)) = 1 := Classical.choose_spec (hsurj 1)
          show π ((hsurj 1).choose • n) = π n
          rw [((hwell 1 n 1 (Classical.choose (hsurj 1)) (by simp) hspec).symm), one_smul]
        simp only [φ]
        rw [TensorProduct.lift.tmul]
        exact hB1 ▸ rfl
      -- Now prove the inclusion
      intro m hm
      have : φ ((TensorProduct.mk A C M) 1 m) = 0 := by
        rw [hm]; exact map_zero φ
      rw [show (TensorProduct.mk A C M) 1 m = 1 ⊗ₜ[A] m by rfl] at this
      rw [hφ_tmul] at this
      simp only [π] at this
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this
    · -- I • M → kernel
      intro x hx
      simp only [LinearMap.mem_ker]
      have h_tmul : ∀ k ∈ I, ∀ m : M, ((TensorProduct.mk A C M) 1) (k • m) = 0 := by
        intro k hk m
        simp only [TensorProduct.mk_apply]
        rw [TensorProduct.tmul_smul]
        have heq : k • (1 : C) = algebraMap A C k := by rw [Algebra.smul_def, mul_one]
        show (k • (1 : C)) ⊗ₜ[A] m = 0
        rw [heq, RingHom.mem_ker.mp hk]
        rw [TensorProduct.zero_tmul]
      -- x ∈ I • M means x is a linear combination of elements of the form k • m
      have : I • (⊤ : Submodule A M) ≤ LinearMap.ker ((TensorProduct.mk A C M) 1) := by
        rw [Submodule.smul_le]
        intro k hk m _
        exact h_tmul k hk m
      exact this hx

private theorem quotientTensor_to_baseChangedQuotient
    (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] :
    ∃ e : ((M ⊗[A] B) ⧸ (I • (⊤ : Submodule A (M ⊗[A] B)))) ≃ₗ[A]
        B ⊗[A] (M ⧸ (I • (⊤ : Submodule A M))),
      e.toLinearMap.comp ((I • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp
        (toTensor A B M)) =
        (TensorProduct.mk A B (M ⧸ (I • (⊤ : Submodule A M))) 1).comp
          (I • (⊤ : Submodule A M)).mkQ := by
  let mkQ_M := (I • (⊤ : Submodule A M)).mkQ
  -- Forward: M ⊗ B → B ⊗ (M / IM) via m ⊗ b ↦ b ⊗ mkQ(m)
  -- Use TensorProduct.lift with a bilinear map
  -- Define bilinear map: M × B → B ⊗ (M ⧸ I • ⊤) by (m, b) ↦ b ⊗ mkQ(m)
  -- TensorProduct.mk A B (M ⧸ I • ⊤) : B →ₗ[A] (M ⧸ I • ⊤) →ₗ[A] B ⊗[A] (M ⧸ I • ⊤)
  let fB := TensorProduct.mk A B (M ⧸ (I • (⊤ : Submodule A M)))
  -- fB.flip : (M ⧸ I • ⊤) →ₗ[A] B →ₗ[A] B ⊗[A] (M ⧸ I • ⊤)
  -- Compose with mkQ_M : M →ₗ (M ⧸ I • ⊤)
  let bilinear := fB.flip.comp mkQ_M
  -- Use TensorProduct.lift to get M ⊗ B → B ⊗ (M ⧸ I • ⊤)
  let fwd : M ⊗[A] B →ₗ[A] B ⊗[A] (M ⧸ (I • (⊤ : Submodule A M))) := TensorProduct.lift bilinear
  -- Show fwd ∘ toTensor = (TensorProduct.mk A B (M ⧸ I • ⊤)) 1 ∘ mkQ
  have hfwd_toTensor : fwd.comp (toTensor A B M) =
      (TensorProduct.mk A B (M ⧸ (I • (⊤ : Submodule A M))) 1).comp mkQ_M := by
    ext m
    simp [fwd, bilinear, fB, toTensor]
  -- Show fwd is surjective
  have hfwd_surj : Function.Surjective fwd := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero fwd⟩
    | tmul b y =>
      obtain ⟨m, hm⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A M)) y
      refine ⟨m ⊗ₜ b, ?_⟩
      simp [fwd, bilinear, fB]
      rw [hm]
    | add x₁ x₂ h₁ h₂ =>
      obtain ⟨x₁', hx₁'⟩ := h₁
      obtain ⟨x₂', hx₂'⟩ := h₂
      exact ⟨x₁' + x₂', by simp [hx₁', hx₂', map_add fwd]⟩
  -- Show I • ⊤ ≤ ker fwd
  have hfwd_ker : I • (⊤ : Submodule A (M ⊗[A] B)) ≤ LinearMap.ker fwd := by
    rw [Submodule.smul_le]
    intro r hr x _
    simp only [LinearMap.mem_ker]
    rw [map_smul]
    -- r • fwd(x) = 0 because fwd(x) ∈ B ⊗ (M ⧸ I • ⊤) and r acts as 0 on M ⧸ I • ⊤
    have h : ∀ y : B ⊗[A] (M ⧸ (I • (⊤ : Submodule A M))), r • y = 0 := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul b z =>
        -- r • (b ⊗ z) = (r • b) ⊗ z = b ⊗ (r • z) in B ⊗[A] (M ⧸ I • ⊤)
        -- Since z ∈ M ⧸ I • ⊤, r • z = mkQ(r • m) = 0 for any lift m of z
        rw [← TensorProduct.tmul_smul]
        -- Need to show b ⊗ₜ (r • z) = 0 where r • z = 0 in M ⧸ I • ⊤
        have hrz : r • z = 0 := by
          obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A M)) z
          have hlin : r • (Submodule.mkQ (I • (⊤ : Submodule A M)) m) =
              Submodule.mkQ (I • (⊤ : Submodule A M)) (r • m) :=
            LinearMap.map_smul ((I • (⊤ : Submodule A M)).mkQ) r m
          rw [hlin]
          exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule A M))).mpr (Submodule.smul_mem_smul hr Submodule.mem_top)
        simp [hrz]
      | add y₁ y₂ h₁ h₂ => simp [h₁, h₂]
    exact h _
  -- Now construct the isomorphism using Submodule.liftQ
  -- fwd factors through (M ⊗ B) ⧸ (I • ⊤)
  let fwd_lifted := Submodule.liftQ _ fwd hfwd_ker
  -- fwd_lifted : (M ⊗ B) ⧸ (I • ⊤) → B ⊗ (M ⧸ I • ⊤)
  have hfwd_lifted_surj : Function.Surjective fwd_lifted := by
    intro y
    obtain ⟨x, hx⟩ := hfwd_surj y
    exact ⟨(I • (⊤ : Submodule A (M ⊗[A] B))).mkQ x, by simp [fwd_lifted, hx]⟩
  -- Need to show fwd_lifted is injective
  -- We have fwd_lifted ∘ (I • ⊤).mkQ = fwd
  have hfwd_lifted_comp : fwd_lifted.comp ((I • (⊤ : Submodule A (M ⊗[A] B))).mkQ) = fwd := by
    rfl
  -- So fwd_lifted ∘ (I • ⊤).mkQ ∘ toTensor = fwd ∘ toTensor = (TensorProduct.mk) 1 ∘ mkQ
  have hfwd_lifted_comm : (fwd_lifted.comp ((I • (⊤ : Submodule A (M ⊗[A] B))).mkQ)).comp (toTensor A B M) =
      (TensorProduct.mk A B (M ⧸ (I • (⊤ : Submodule A M))) 1).comp mkQ_M := by
    rw [hfwd_lifted_comp, hfwd_toTensor]
  -- Construct backward map: B ⊗ (M ⧸ I • ⊤) → (M ⊗ B) ⧸ (I • ⊤)
  let mkQMB := (I • (⊤ : Submodule A (M ⊗[A] B))).mkQ
  -- For each b : B, define ψ_b : M ⧸ I • ⊤ → (M ⊗ B) ⧸ (I • ⊤) by ψ_b(y) = mkQMB(m ⊗ b) where y = mkQ(m)
  -- First, for each b, define M → (M ⊗ B) ⧸ (I • ⊤) by m ↦ mkQMB(m ⊗ b)
  let psi_for_b : B → (M →ₗ[A] ((M ⊗[A] B) ⧸ (I • (⊤ : Submodule A (M ⊗[A] B))))) := fun b =>
    mkQMB.comp (TensorProduct.mk A M B |>.flip b)
  -- This is linear in m
  have hpsi_linear : ∀ b : B, ∀ r : A, ∀ m₁ m₂ : M, psi_for_b b (r • m₁ + m₂) = r • psi_for_b b m₁ + psi_for_b b m₂ := by
    intros; simp [psi_for_b]
  have hpsi_add : ∀ b₁ b₂ : B, ∀ m : M, psi_for_b (b₁ + b₂) m = psi_for_b b₁ m + psi_for_b b₂ m := by
    intros; simp [psi_for_b]
  have hpsi_smul : ∀ r : A, ∀ b : B, ∀ m : M, psi_for_b (r • b) m = r • psi_for_b b m := by
    intros; simp [psi_for_b]
  -- And psi_for_b b factors through M ⧸ I • ⊤
  have hpsi_factors : ∀ b : B, ∀ m ∈ I • (⊤ : Submodule A M), psi_for_b b m = 0 := by
    intro b m hm
    simp only [psi_for_b, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.flip_apply]
    have h_mem : m ⊗ₜ[A] b ∈ I • (⊤ : Submodule A (M ⊗[A] B)) := by
      -- Use TensorProduct.linearMap to convert this to a submodule membership problem
      let linMap : M →ₗ[A] M ⊗[A] B := TensorProduct.mk A M B |>.flip b
      -- linMap is linear, so it preserves submodule membership
      -- Show linMap (I • ⊤) ≤ I • (M ⊗ B)
      have hle : (I • (⊤ : Submodule A M)).map linMap ≤ I • (⊤ : Submodule A (M ⊗[A] B)) := by
        rw [Submodule.map_le_iff_le_comap]
        have key : (I • (⊤ : Submodule A M)) ≤ Submodule.comap linMap (I • ⊤) := by
          rw [Submodule.smul_le]
          intro r hr m _
          simp [linMap]
          exact Submodule.smul_mem_smul hr (Submodule.mem_top : (m ⊗ₜ b) ∈ ⊤)
        exact key
      have hlin : linMap m ∈ Submodule.map linMap (I • (⊤ : Submodule A M)) := by
        apply Submodule.mem_map.mpr
        exact ⟨m, hm, rfl⟩
      exact hle hlin
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h_mem
  -- Define backward map: for each b, we have ψ_b : M → (M ⊗ B) ⧸ (I • M ⊗ B)
  -- This factors through M ⧸ I • M, giving ψ_b' : M ⧸ I • M → (M ⊗ B) ⧸ (I • M ⊗ B)
  let psi_for_b' : B → (M ⧸ I • (⊤ : Submodule A M)) →ₗ[A] ((M ⊗[A] B) ⧸ (I • (⊤ : Submodule A (M ⊗[A] B)))) := fun b =>
    Submodule.liftQ _ (psi_for_b b) (hpsi_factors b)
  -- Variants for psi_for_b' on the quotient
  have hpsi'_add : ∀ b₁ b₂ : B, psi_for_b' (b₁ + b₂) = psi_for_b' b₁ + psi_for_b' b₂ := by
    intro b₁ b₂
    apply LinearMap.ext
    intro y
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A M)) y
    simp [psi_for_b', hpsi_add]
  have hpsi'_smul : ∀ r : A, ∀ b : B, psi_for_b' (r • b) = r • psi_for_b' b := by
    intro r b
    apply LinearMap.ext
    intro y
    obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A M)) y
    simp [psi_for_b', hpsi_smul]
  -- Build backward: B ⊗ (M ⧸ I • M) → (M ⊗ B) ⧸ (I • M ⊗ B)
  -- Define a bilinear map from B × (M ⧸ I • ⊤) to (M ⊗ B) ⧸ (I • M ⊗ B)
  let bilinearBack := LinearMap.mk₂ A (fun b y => psi_for_b' b y)
    (fun b₁ b₂ y => by simp [hpsi'_add])
    (fun r b y => by simp [hpsi'_smul])
    (fun b y₁ y₂ => by simp [psi_for_b'])
    (fun r b y => by exact LinearMap.map_smul _ _ _)
  let backward := TensorProduct.lift bilinearBack
  -- fwd_lifted is surjective, we need to show it's injective
  -- Use that backward is a right inverse
  have hfwd_backward : fwd_lifted.comp backward = LinearMap.id := by
    apply LinearMap.ext
    intro x
    -- Prove by induction on x ∈ B ⊗ (M ⧸ I • ⊤)
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      -- y is in the quotient, get a representative
      rcases Submodule.mkQ_surjective (I • (⊤ : Submodule A M)) y with ⟨m, rfl⟩
      simp [backward, bilinearBack, psi_for_b']
      -- Goal: fwd_lifted (psi_for_b b m) = b ⊗ mkQ m
      -- psi_for_b b m = mkQMB (m ⊗ b)
      simp only [psi_for_b, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.flip_apply]
      -- fwd_lifted (mkQMB (m ⊗ b)) = fwd (m ⊗ b)
      simp only [mkQMB]
      have h := LinearMap.congr_fun hfwd_lifted_comp (m ⊗ₜ[A] b)
      simp only [LinearMap.comp_apply] at h
      rw [h]
      simp [fwd, bilinear, fB]
      rfl
    | add x₁ x₂ h₁ h₂ => simp [map_add, h₁, h₂]
  have hbackward_fwd : backward.comp fwd_lifted = LinearMap.id := by
    -- We prove this by showing that for generators of (M ⊗ B) ⧸ (I • ⊤),
    -- backward (fwd_lifted (mkQ x)) = mkQ x
    apply LinearMap.ext
    intro x
    -- x is in the quotient, so x = mkQ y for some y
    rcases Submodule.mkQ_surjective (I • (⊤ : Submodule A (M ⊗[A] B))) x with ⟨y, rfl⟩
    simp [fwd_lifted, backward, bilinearBack]
    -- Now need to show: backward (fwd y) = mkQ y for y : M ⊗ B
    -- Prove by induction on y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul m b =>
      -- fwd (m ⊗ b) = b ⊗ mkQ m
      simp [fwd, bilinear, fB, backward, bilinearBack, psi_for_b']
      -- Goal: ((I • ⊤).liftQ (psi_for_b b) ...) (mkQ_M m) = mkQ (m ⊗ b)
      have h := Submodule.liftQ_mkQ (I • (⊤ : Submodule A M)) (psi_for_b b) (hpsi_factors b)
      simp only [mkQ_M]
      rw [← LinearMap.comp_apply]
      rw [LinearMap.congr_fun h m]
      simp only [psi_for_b, LinearMap.comp_apply, TensorProduct.mk_apply, LinearMap.flip_apply, mkQMB]
      rfl
    | add x₁ x₂ h₁ h₂ => simp [h₁, h₂]
  let e : ((M ⊗[A] B) ⧸ (I • (⊤ : Submodule A (M ⊗[A] B)))) ≃ₗ[A] B ⊗[A] (M ⧸ (I • (⊤ : Submodule A M))) :=
    LinearEquiv.ofLinear fwd_lifted backward hfwd_backward hbackward_fwd
  let backward := TensorProduct.lift bilinearBack
  exact ⟨e, by simpa [mkQ_M] using hfwd_lifted_comm⟩

private theorem quotientAlgebraTensor_equiv_baseChangedQuotient
    (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] :
    ∃ e : ((B ⧸ I.map (algebraMap A B)) ⊗[A] M) ≃ₗ[A]
        B ⊗[A] (M ⧸ (I • (⊤ : Submodule A M))),
      e.toLinearMap.comp
          ((TensorProduct.mk A (B ⧸ I.map (algebraMap A B)) M) 1) =
        (TensorProduct.mk A B (M ⧸ (I • (⊤ : Submodule A M))) 1).comp
          (I • (⊤ : Submodule A M)).mkQ := by
  set I' := Ideal.map (algebraMap A B) I with hI'
  -- Define a bilinear map B × M → B ⊗[A] (M ⧸ (I • ⊤))
  -- (b, m) ↦ b ⊗ (m + IM)
  let φ : B →ₗ[A] M →ₗ[A] B ⊗[A] (M ⧸ (I • (⊤ : Submodule A M))) :=
    { toFun := fun b =>
        { toFun := fun m => b ⊗ₜ[A] (I • (⊤ : Submodule A M)).mkQ m
          map_add' := by intros; rw [map_add, TensorProduct.tmul_add]
          map_smul' := by intros; simp [TensorProduct.tmul_smul] }
      map_add' := by intros; ext m; simp [TensorProduct.add_tmul]
      map_smul' := by intros; rfl }
  -- Lift to a linear map B ⊗[A] M → B ⊗[A] (M ⧸ (I • ⊤))
  let ψ : B ⊗[A] M →ₗ[A] B ⊗[A] (M ⧸ (I • (⊤ : Submodule A M))) := TensorProduct.lift φ
  -- Show ψ vanishes on I' ⊗ M
  have hψ_gen : ∀ a ∈ I, ∀ m : M, ψ ((algebraMap A B a) ⊗ₜ[A] m) = 0 := by
    intro a ha m
    simp only [ψ, TensorProduct.lift.tmul]
    -- (algebraMap A B a) ⊗ (m + IM) = a • 1 ⊗ (m + IM) = 1 ⊗ (a • (m + IM)) = 1 ⊗ (am + IM) = 0
    have hmem : a • m ∈ I • (⊤ : Submodule A M) := by
      apply Submodule.smul_mem_smul ha
      trivial
    show (algebraMap A B a) ⊗ₜ[A] (I • (⊤ : Submodule A M)).mkQ m = 0
    rw [show (algebraMap A B a) = a • (1 : B) by rw [Algebra.smul_def, mul_one]]
    have heq : (a • (1 : B)) ⊗ₜ[A] (I • (⊤ : Submodule A M)).mkQ m =
           (1 : B) ⊗ₜ[A] (a • (I • (⊤ : Submodule A M)).mkQ m) := by
      rw [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
    rw [heq]
    have hzero : a • (I • (⊤ : Submodule A M)).mkQ m = 0 := by
      rw [show a • (I • (⊤ : Submodule A M)).mkQ m = (I • (⊤ : Submodule A M)).mkQ (a • m) by rfl]
      show Submodule.Quotient.mk (a • m) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact hmem
    rw [hzero, TensorProduct.tmul_zero]
  -- Define the backward bilinear map B × M → (B ⧸ I') ⊗[A] M
  -- (b, m) ↦ (b + I') ⊗ m
  -- Then show it vanishes on B × (I • M) to get a map B ⊗[A] (M ⧸ (I • M)) → (B ⧸ I') ⊗[A] M
  let φb : B →ₗ[A] M →ₗ[A] (B ⧸ I') ⊗[A] M :=
    { toFun := fun b =>
        { toFun := fun m => (Ideal.Quotient.mk I' b) ⊗ₜ[A] m
          map_add' := by intros; rw [TensorProduct.tmul_add]
          map_smul' := by intros; simp [TensorProduct.tmul_smul] }
      map_add' := by intros; ext; simp [TensorProduct.add_tmul]
      map_smul' := by intros; rfl }
  -- φb vanishes on B × (I • M): for b ∈ B, x ∈ I • M, φb(b)(x) = 0
  have hφb_I : ∀ b : B, ∀ x ∈ (I • (⊤ : Submodule A M)), φb b x = 0 := by
    intro b x hx
    -- Define the linear map φb b : M → (B ⧸ I') ⊗[A] M
    let φb_b : M →ₗ[A] (B ⧸ I') ⊗[A] M := φb b
    -- For a ∈ I, m ∈ M: φb b (a • m) = a • φb b m = 0 by the key lemma
    have key : ∀ a ∈ I, ∀ m : M, φb_b (a • m) = 0 := by
      intro a ha m
      rw [φb_b.map_smul]
      -- φb_b m = (Ideal.Quotient.mk I') b ⊗ₜ[A] m
      -- Need to show a • ((Ideal.Quotient.mk I') b ⊗ₜ[A] m) = 0
      have hu : φb_b m = (Ideal.Quotient.mk I') b ⊗ₜ[A] m := rfl
      rw [hu, TensorProduct.smul_tmul']
      -- Need to show a • (Ideal.Quotient.mk I') b ⊗ₜ m = 0
      have hzero : a • ((Ideal.Quotient.mk I') b) = 0 := by
        have : a • ((Ideal.Quotient.mk I') b) = (Ideal.Quotient.mk I') (a • b) := rfl
        rw [this]
        rw [Ideal.Quotient.eq_zero_iff_mem]
        have hmem : algebraMap A B a ∈ I' := by
          rw [hI']
          exact Ideal.subset_span ⟨a, ha, rfl⟩
        have hmul : algebraMap A B a * b ∈ I' := I'.mul_mem_right b hmem
        simp only [Algebra.smul_def]
        exact hmul
      rw [hzero, TensorProduct.zero_tmul]
    -- I • ⊤ ⊆ ker(φb b) because φb b (a • m) = 0 for all a ∈ I, m ∈ M
    -- φb_b is linear, so it suffices to show it vanishes on generators a • m for a ∈ I
    have hker : I • (⊤ : Submodule A M) ≤ LinearMap.ker φb_b := by
      rw [Submodule.smul_le]
      intro r hr m _
      exact key r hr m
    exact hker hx
  -- Forward map: (B ⧸ I') ⊗[A] M → B ⊗[A] (M ⧸ (I • ⊤)) induced by ψ
  -- ψ vanishes on I' ⊗ M, so we can use the right exactness of tensor product
  -- First show ψ vanishes on all of I' • ⊤ in B ⊗[A] M
  -- Note: I' ⊗ M → B ⊗[A] M has image I' • (image of M in B ⊗[A] M)
  -- Actually, the image of I' ⊗ M in B ⊗ M is contained in I' • (1 ⊗ M)
  -- We use that ψ(1 ⊗ m) = mkQ m, and for a ∈ I: ψ(a • (1 ⊗ m)) = a • ψ(1 ⊗ m) = a • mkQ m = 0
  have hψ_I' : ∀ x ∈ Submodule.span A (Set.range fun p : I × M => (algebraMap A B p.1) ⊗ₜ[A] p.2), ψ x = 0 := fun x hx => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact hψ_gen p.1.val p.1.prop p.2
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy, zero_add]
    | smul r x _ hx => rw [map_smul, hx, smul_zero]
  -- Forward map: (B ⧸ I') ⊗[A] M → B ⊗[A] (M ⧸ (I • ⊤))
  -- Define bilinear map (B ⧸ I') × M → B ⊗[A] (M ⧸ (I • ⊤)) by [b] ⊗ m ↦ ψ(b ⊗ m)
  -- For each m, the map b ↦ ψ(b ⊗ m) vanishes on I'
  -- So it factors through B ⧸ I'
  have hvanish_aux : ∀ a ∈ I, ∀ m : M, (algebraMap A B a) ⊗ₜ[A] (I • (⊤ : Submodule A M)).mkQ m = 0 := by
    intro a ha m
    exact hψ_gen a ha m
  have hvanish : ∀ m : M, ∀ b' ∈ I', ψ (b' ⊗ₜ[A] m) = 0 := by
    intro m b' hb'
    simp only [ψ, TensorProduct.lift.tmul]
    -- b' ∈ I' = Ideal.map (algebraMap A B) I = Submodule.span B ((algebraMap A B) '' I)
    -- First express I' as a submodule span
    have hI'span : I' = Submodule.span B ((algebraMap A B) '' I) := by
      rw [hI']
      rfl
    rw [hI'span] at hb'
    induction hb' using Submodule.span_induction with
    | mem x hx =>
      rw [Set.mem_image] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      exact hvanish_aux a ha m
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul r x _ hx =>
      -- φ (r • x) m = (r • x) ⊗ₜ (mkQ m)
      -- hx : (φ x) m = 0, which means x ⊗ₜ (mkQ m) = 0
      have hx' : x ⊗ₜ[A] ((I • (⊤ : Submodule A M)).mkQ) m = 0 := hx
      have heq : (φ (r • x)) m = (r • x) ⊗ₜ[A] ((I • (⊤ : Submodule A M)).mkQ) m := rfl
      rw [heq]
      rw [show (r • x) ⊗ₜ[A] ((I • (⊤ : Submodule A M)).mkQ) m = r • (x ⊗ₜ[A] ((I • (⊤ : Submodule A M)).mkQ) m) by
        rw [TensorProduct.smul_tmul']
      ]
      rw [hx']
      simp
  -- Define forward bilinear map (B ⧸ I') × M → B ⊗[A] (M ⧸ (I • ⊤))
  -- For each m, we have fm : B →ₗ[A] B ⊗[A] (M ⧸ (I • ⊤)) given by fm(b) = ψ(b ⊗ m)
  -- fm vanishes on I', so it factors through B ⧸ I'
  let fm : ∀ m : M, B →ₗ[A] B ⊗[A] (M ⧸ (I • (⊤ : Submodule A M))) := fun m =>
    ψ.comp ((TensorProduct.mk A B M).flip m)
  have hfm_vanish : ∀ m : M, ∀ b' ∈ I', (fm m) b' = 0 := by
    intro m b' hb'
    exact hvanish m b' hb'
  -- Define a bilinear map (B ⧸ I') × M → B ⊗[A] (M ⧸ I • ⊤)
  -- First define on representatives B × M → B ⊗[A] (M ⧸ I • ⊤)
  -- fm is linear in m: fm : M →ₗ[A] (B →ₗ[A] B ⊗[A] (M ⧸ I • ⊤))
  -- fm m = ψ ∘ₗ (TensorProduct.mk A B M).flip m
  have hfm_add : ∀ m₁ m₂ : M, fm (m₁ + m₂) = fm m₁ + fm m₂ := by
    intro m₁ m₂; ext b
    simp [fm, LinearMap.add_apply, LinearMap.comp_apply]
  have hfm_smul : ∀ r : A, ∀ m : M, fm (r • m) = r • fm m := by
    intro r m; ext b
    simp [fm, LinearMap.smul_apply, LinearMap.comp_apply]
  let repBilin : B →ₗ[A] M →ₗ[A] B ⊗[A] (M ⧸ (I • (⊤ : Submodule A M))) :=
    { toFun := fun b =>
        { toFun := fun m => (fm m) b
          map_add' := fun m₁ m₂ => by simp [hfm_add]
          map_smul' := fun r m => by simp [hfm_smul] }
      map_add' := fun b₁ b₂ =>
        LinearMap.ext fun m => by simp [LinearMap.add_apply]
      map_smul' := fun r b =>
        LinearMap.ext fun m => by simp [LinearMap.smul_apply] }
  have hrepBilin_van : ∀ b ∈ I', repBilin b = 0 := fun b hb => LinearMap.ext fun m => by simp [repBilin]; exact hfm_vanish m b hb
  let fwd_ℓ := Submodule.liftQ (Submodule.restrictScalars A I') repBilin (by intro b hb; exact LinearMap.mem_ker.mpr (hrepBilin_van b hb))
  let fwd := TensorProduct.lift fwd_ℓ
  -- Backward map: B ⊗[A] (M ⧸ I • ⊤) → (B ⧸ I') ⊗[A] M
  -- Use φb which vanishes on I • ⊤
  -- For each b : B, φb b : M → (B ⧸ I') ⊗[A] M vanishes on I • ⊤
  have hφb_b_van : ∀ b : B, I • (⊤ : Submodule A M) ≤ LinearMap.ker (φb b) := by
    intro b
    rw [Submodule.smul_le]
    intro r hr m _
    exact hφb_I b (r • m) (Submodule.smul_mem_smul hr (Submodule.mem_top : m ∈ ⊤))
  -- Define back_ℓ b for each b
  let back_ℓ' : B → (M ⧸ (I • ⊤)) →ₗ[A] (B ⧸ I') ⊗[A] M := fun b => Submodule.liftQ (I • ⊤) (φb b) (hφb_b_van b)
  -- Prove back_ℓ' is linear in b
  have hback_ℓ'_add : ∀ b₁ b₂ : B, back_ℓ' (b₁ + b₂) = back_ℓ' b₁ + back_ℓ' b₂ := by
    intro b₁ b₂; ext m; simp [back_ℓ']
  have hback_ℓ'_smul : ∀ r : A, ∀ b : B, back_ℓ' (r • b) = r • back_ℓ' b := by
    intro r b; ext m; simp [back_ℓ', LinearMap.smul_apply]
  let backB : B →ₗ[A] (M ⧸ (I • ⊤)) →ₗ[A] (B ⧸ I') ⊗[A] M :=
    { toFun := back_ℓ', map_add' := hback_ℓ'_add, map_smul' := hback_ℓ'_smul }
  let back := TensorProduct.lift backB
  -- Show fwd and back are inverses
  -- fwd([b] ⊗ m) = ψ(b ⊗ m) = b ⊗ mkQ m
  -- back(b ⊗ [m]) = (b + I') ⊗ₜ m
  have back_comp_fwd : back ∘ₗ fwd = LinearMap.id := by
    ext x y
    simp only [LinearMap.comp_apply, LinearMap.id_coe]
    -- fwd (mk x ⊗ y) = fwd_ℓ x y = repBilin x y = fm y x = ψ (x ⊗ y) = x ⊗ mkQ y
    -- back (x ⊗ mkQ y) = backB x (mkQ y) = back_ℓ' x (mkQ y) = φb x y = (x + I') ⊗ y = mk x ⊗ y
    simp only [fwd, TensorProduct.lift.tmul, fwd_ℓ, Submodule.liftQ_mkQ]
    simp only [back, TensorProduct.lift.tmul, backB, back_ℓ', Submodule.liftQ_mkQ]
    rfl
  have fwd_comp_back : fwd ∘ₗ back = LinearMap.id := by
    ext x y
    simp only [LinearMap.comp_apply, LinearMap.id_coe]
    -- back (x ⊗ mkQ y) = backB x (mkQ y) = back_ℓ' x (mkQ y) = φb x y = (x + I') ⊗ y = mk x ⊗ y
    -- fwd (mk x ⊗ y) = fwd_ℓ x y = repBilin x y = fm y x = ψ (x ⊗ y) = x ⊗ mkQ y
    simp only [back, TensorProduct.lift.tmul, backB, back_ℓ', Submodule.liftQ_mkQ]
    simp only [fwd, TensorProduct.lift.tmul, fwd_ℓ, Submodule.liftQ_mkQ]
    rfl
  -- Construct the equivalence
  use {
    toFun := fwd
    invFun := back
    left_inv := fun x => show (back ∘ₗ fwd) x = x from by rw [back_comp_fwd]; rfl
    right_inv := fun x => show (fwd ∘ₗ back) x = x from by rw [fwd_comp_back]; rfl
    map_add' := fwd.map_add
    map_smul' := fwd.map_smul
  }
  -- Prove commutativity
  ext m
  simp only [LinearMap.comp_apply, LinearMap.id_coe]
  -- fwd ((mkQ 1) m) = fwd (1 ⊗ mkQ m) = fwd_ℓ 1 (mkQ m) = repBilin 1 (mkQ m) = fm (mkQ m) 1
  --                   = ψ(1 ⊗ m) = 1 ⊗ mkQ m
  simp only [fwd, TensorProduct.lift.tmul, fwd_ℓ, Submodule.liftQ_mkQ]
  rfl

private theorem quotientTensor_baseChange_equiv
    (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (I : Ideal A)
    (M : Type u) [AddCommGroup M] [Module A M] :
    ∃ e : ((M ⊗[A] B) ⧸ (I • (⊤ : Submodule A (M ⊗[A] B)))) ≃ₗ[A]
        (B ⧸ I.map (algebraMap A B)) ⊗[A] M,
      e.toLinearMap.comp ((I • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp
        (toTensor A B M)) = (TensorProduct.mk A (B ⧸ I.map (algebraMap A B)) M) 1 := by
  -- Use quotientTensor_to_baseChangedQuotient and quotientAlgebraTensor_equiv_baseChangedQuotient
  obtain ⟨e1, he1⟩ := quotientTensor_to_baseChangedQuotient A B I M
  obtain ⟨e2, he2⟩ := quotientAlgebraTensor_equiv_baseChangedQuotient A B I M
  -- We need (M ⊗ B) ⧸ (I • ⊤) ≃ (B ⧸ I.map _) ⊗ M
  -- e1 : (M ⊗ B) ⧸ (I • ⊤) ≃ B ⊗ (M ⧸ (I • ⊤))
  -- e2 : (B ⧸ I.map _) ⊗ M ≃ B ⊗ (M ⧸ (I • ⊤))
  -- So e1.trans e2.symm : (M ⊗ B) ⧸ (I • ⊤) ≃ (B ⧸ I.map _) ⊗ M
  use e1.trans e2.symm
  ext x
  show e2.symm (e1 ((I • (⊤ : Submodule A (M ⊗[A] B))).mkQ ((toTensor A B M) x))) =
      ((TensorProduct.mk A (B ⧸ I.map (algebraMap A B)) M) 1) x
  have h1 : e1 ((I • (⊤ : Submodule A (M ⊗[A] B))).mkQ ((toTensor A B M) x)) =
      ((TensorProduct.mk A B (M ⧸ (I • (⊤ : Submodule A M)))) 1) ((I • (⊤ : Submodule A M)).mkQ x) :=
    LinearMap.congr_fun he1 x
  have h2 : e2 (((TensorProduct.mk A (B ⧸ I.map (algebraMap A B)) M) 1) x) =
      ((TensorProduct.mk A B (M ⧸ (I • (⊤ : Submodule A M)))) 1) ((I • (⊤ : Submodule A M)).mkQ x) :=
    LinearMap.congr_fun he2 x
  rw [h1, ← h2]
  exact e2.symm_apply_apply _

private theorem baseChange_quotient_equiv
    (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (I : Ideal A)
    (hsurj : Function.Surjective
      (algebraMap A (B ⧸ I.map (algebraMap A B))))
    (hker : RingHom.ker
      (algebraMap A (B ⧸ I.map (algebraMap A B))) = I)
    (M : Type u) [AddCommGroup M] [Module A M] :
    ∃ e : ((M ⊗[A] B) ⧸ (I • (⊤ : Submodule A (M ⊗[A] B)))) ≃ₗ[A]
        M ⧸ (I • (⊤ : Submodule A M)),
      e.toLinearMap.comp ((I • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp
        (toTensor A B M)) = (I • (⊤ : Submodule A M)).mkQ := by
  obtain ⟨e₁, he₁⟩ := quotientTensor_baseChange_equiv A B I M
  let g := (TensorProduct.mk A (B ⧸ I.map (algebraMap A B)) M) 1
  obtain ⟨hg_surj, hg_ker⟩ := tensorMk_bijective_of_surjective A
    (B ⧸ I.map (algebraMap A B)) hsurj M
  have hg_ker' : LinearMap.ker g = I • (⊤ : Submodule A M) := by
    rw [hg_ker, hker]
  let qeq : (M ⧸ LinearMap.ker g) ≃ₗ[A] M ⧸ (I • (⊤ : Submodule A M)) :=
    Submodule.quotEquivOfEq _ _ hg_ker'
  let e₂ : ((B ⧸ I.map (algebraMap A B)) ⊗[A] M) ≃ₗ[A]
      M ⧸ (I • (⊤ : Submodule A M)) :=
    (LinearMap.quotKerEquivOfSurjective g hg_surj).symm.trans qeq
  use e₁.trans e₂
  ext x
  change e₂ (e₁ ((I • (⊤ : Submodule A (M ⊗[A] B))).mkQ ((toTensor A B M) x))) = _
  rw [show e₁ ((I • (⊤ : Submodule A (M ⊗[A] B))).mkQ ((toTensor A B M) x)) = g x by
    exact LinearMap.congr_fun he₁ x]
  change qeq ((LinearMap.quotKerEquivOfSurjective g hg_surj).symm (g x)) = _
  have hq : qeq (Submodule.Quotient.mk x) =
      (I • (⊤ : Submodule A M)).mkQ x :=
    Submodule.quotEquivOfEq_mk _ _ hg_ker' x
  rw [← hq]
  congr 1
  exact (LinearEquiv.symm_apply_eq _).mpr rfl

/-- Reduction mod `f^n` is insensitive to completion-like base change: the composite
`M → M ⊗ B → (M ⊗ B)/f^n(M ⊗ B)` is surjective with kernel `f^n M`.
(Base change of the isomorphism `A/f^n ≅ B/f^nB`.) -/
theorem quotSMulTop_baseChange_bijective
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (M : Type u) [AddCommGroup M] [Module A M] (n : ℕ) (hn : 0 < n) :
    Function.Surjective
        ((Ideal.span {f ^ n} • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp (toTensor A B M)) ∧
      LinearMap.ker
          ((Ideal.span {f ^ n} • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp (toTensor A B M)) =
        Ideal.span {f ^ n} • (⊤ : Submodule A M) := by
  let I : Ideal A := Ideal.span {f ^ n}
  let q := (I • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp (toTensor A B M)
  obtain ⟨e, he⟩ := baseChange_quotient_equiv A B I (hB.surjective_mod n hn)
    (hB.ker_mod n hn) M
  have he_apply (x : M) : e (q x) = (I • (⊤ : Submodule A M)).mkQ x := by
    exact LinearMap.congr_fun he x
  constructor
  · intro y
    obtain ⟨x, hx⟩ := (I • (⊤ : Submodule A M)).mkQ_surjective (e y)
    refine ⟨x, e.injective ?_⟩
    rw [he_apply, hx]
  · change LinearMap.ker q = I • (⊤ : Submodule A M)
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      have hz : e (q x) = 0 := by rw [hx, map_zero]
      rw [he_apply] at hz
      exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule A M))).mp hz
    · intro hx
      apply e.injective
      rw [he_apply, map_zero]
      exact (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule A M))).mpr hx
/- ===== node D04 (D04_a1): verified by Aristotle ===== -/
private lemma powers_smul_injective
    (A : Type u) [CommRing A] (f : A)
    (N : Type u) [AddCommGroup N] [Module A N]
    (hf : IsSMulRegular N f) (s : Submonoid.powers f) :
    Function.Injective (fun x : N => (s : A) • x) := by
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (s : A) f).mp s.property
  rw [← hk]
  exact hf.pow k

private lemma localized_eq_implies_relation
    (A : Type u) [CommRing A] (f : A)
    (N : Type u) [AddCommGroup N] [Module A N]
    (hf : IsSMulRegular N f) (s : Submonoid.powers f) (m v : N)
    (h : LocalizedModule.mk m s = LocalizedModule.mk v 1) :
    m = (s : A) • v := by
  obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.mp h
  apply powers_smul_injective A f N hf t
  simpa [smul_smul] using ht

private lemma sqSnd_sqFst_apply
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] (x : M) :
    sqSnd A f B M (sqFst A f B M x) = 0 := by
  simp [sqSnd, sqFst, toTensor]

private lemma exists_lift_of_power_relation
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M]
    (hMB : IsSMulRegular (M ⊗[A] B) f)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Surjective
          ((Ideal.span {f ^ n} • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp (toTensor A B M)) ∧
        LinearMap.ker
            ((Ideal.span {f ^ n} • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp (toTensor A B M)) =
          Ideal.span {f ^ n} • (⊤ : Submodule A M))
    (k : ℕ) (m : M) (v : M ⊗[A] B)
    (hmv : toTensor A B M m = (f ^ k) • v) :
    ∃ x : M, toTensor A B M x = v ∧ (f ^ k) • x = m := by
  by_cases hk : k = 0
  · subst k
    refine ⟨m, ?_, by simp⟩
    simpa using hmv
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    let Q := Ideal.span {f ^ k} • (⊤ : Submodule A (M ⊗[A] B))
    let q := Q.mkQ.comp (toTensor A B M)
    have hmker : m ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker]
      change Q.mkQ (toTensor A B M m) = 0
      rw [hmv]
      exact (Submodule.Quotient.mk_eq_zero Q).mpr (by
        dsimp [Q]
        rw [Submodule.ideal_span_singleton_smul]
        exact Submodule.smul_mem_pointwise_smul v (f ^ k) ⊤ trivial)
    have hm : m ∈ Ideal.span {f ^ k} • (⊤ : Submodule A M) := by
      rw [← (hquot k hkpos).2]
      exact hmker
    rw [Submodule.ideal_span_singleton_smul] at hm
    obtain ⟨x, -, hxm⟩ :=
      (Submodule.mem_smul_pointwise_iff_exists m (f ^ k) (⊤ : Submodule A M)).mp hm
    refine ⟨x, ?_, hxm⟩
    apply hMB.pow k
    change (f ^ k) • toTensor A B M x = (f ^ k) • v
    rw [← LinearMap.map_smul, hxm, hmv]

/-- Middle exactness of the Beauville-Laszlo square, given that `f` is regular on the
base change `M ⊗ B`.  `hquot` is the statement of node D03. -/
theorem sq_exact_of_smulRegular_baseChange
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (M : Type u) [AddCommGroup M] [Module A M] (hM : IsSMulRegular M f)
    (hMB : IsSMulRegular (M ⊗[A] B) f)
    (hquot : ∀ n : ℕ, 0 < n →
      Function.Surjective
          ((Ideal.span {f ^ n} • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp (toTensor A B M)) ∧
        LinearMap.ker
            ((Ideal.span {f ^ n} • (⊤ : Submodule A (M ⊗[A] B))).mkQ.comp (toTensor A B M)) =
          Ideal.span {f ^ n} • (⊤ : Submodule A M)) :
    Function.Exact (sqFst A f B M) (sqSnd A f B M) := by
  intro z
  constructor
  · intro hz
    rcases z with ⟨u, v⟩
    induction u using LocalizedModule.induction_on with
    | h m s =>
      have hloc : LocalizedModule.mk (toTensor A B M m) s =
          LocalizedModule.mk v 1 := by
        apply sub_eq_zero.mp
        simpa [sqSnd] using hz
      have hrel : toTensor A B M m = (s : A) • v :=
        localized_eq_implies_relation A f (M ⊗[A] B) hMB s _ _ hloc
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (s : A) f).mp s.property
      obtain ⟨x, hx, hxm⟩ :=
        exists_lift_of_power_relation A f B M hMB hquot k m v (by simpa [hk] using hrel)
      refine ⟨x, ?_⟩
      apply Prod.ext
      · change LocalizedModule.mk x 1 = LocalizedModule.mk m s
        apply LocalizedModule.mk_eq.mpr
        refine ⟨1, ?_⟩
        simpa [hk] using hxm
      · simpa [sqFst] using hx
  · rintro ⟨x, rfl⟩
    exact sqSnd_sqFst_apply A f B M x
/- ===== node D05 (D05_a2): verified by Aristotle ===== -/
section Aux

variable {A : Type u} [CommRing A] {f : A} {B : Type u} [CommRing B] [Algebra A B]

/-- Reduction mod `f` is surjective from `A` onto `B/fB`: every `b : B` is congruent to
some `algebraMap A B a` modulo `f`. -/
private lemma exists_algebraMap_add_smul (hB : IsCompletionLike A f B) (b : B) :
    ∃ (a : A) (c : B), b = algebraMap A B a + f • c := by
  -- lift the class of `b` in `B/fB` to an element `a` of `A`
  obtain ⟨a, ha⟩ := hB.surjective_mod 1 one_pos (Ideal.Quotient.mk _ b)
  have ha' : Ideal.Quotient.mk (Ideal.map (algebraMap A B) (Ideal.span {f ^ 1}))
        (algebraMap A B a) =
      Ideal.Quotient.mk (Ideal.map (algebraMap A B) (Ideal.span {f ^ 1})) b := by
    simpa [Algebra.algebraMap_eq_smul_one] using ha
  rw [Ideal.Quotient.eq, pow_one,
    show Ideal.map (algebraMap A B) (Ideal.span {f}) = Ideal.span {algebraMap A B f} by
      rw [Ideal.map_span]; simp,
    Ideal.mem_span_singleton] at ha'
  obtain ⟨c, hc⟩ := ha'
  refine ⟨a, -c, ?_⟩
  rw [Algebra.smul_def]
  linear_combination -hc

/-- Every element of `P ⊗[A] B` is, modulo `f`, of the form `p ⊗ₜ 1`. -/
private lemma exists_tmul_one_add_smul (hB : IsCompletionLike A f B)
    {P : Type u} [AddCommGroup P] [Module A P] (z : P ⊗[A] B) :
    ∃ (p : P) (w : P ⊗[A] B), z = p ⊗ₜ[A] (1 : B) + f • w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul p b =>
    obtain ⟨a, c, hac⟩ := exists_algebraMap_add_smul hB b
    refine ⟨a • p, p ⊗ₜ[A] c, ?_⟩
    rw [hac, TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨p₁, w₁, h₁⟩ := hx
    obtain ⟨p₂, w₂, h₂⟩ := hy
    exact ⟨p₁ + p₂, w₁ + w₂, by rw [h₁, h₂, TensorProduct.add_tmul, smul_add]; abel⟩

/-- The isomorphism `A/(f) ≃+* B/fB` coming from the completion-like hypothesis. -/
private noncomputable def redQuotEquiv (hB : IsCompletionLike A f B) :
    (A ⧸ Ideal.span {f}) ≃+* (B ⧸ (Ideal.span {f ^ 1}).map (algebraMap A B)) :=
  (Ideal.quotEquivOfEq (by rw [hB.ker_mod 1 one_pos, pow_one])).trans
    (RingHom.quotientKerEquivOfSurjective (hB.surjective_mod 1 one_pos))

private lemma redQuotEquiv_mk (hB : IsCompletionLike A f B) (a : A) :
    redQuotEquiv hB (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (algebraMap A B a) := by
  simp [redQuotEquiv, RingHom.quotientKerEquivOfSurjective, Ideal.quotEquivOfEq_mk,
    RingHom.kerLift_mk]

private lemma redQuotEquiv_symm_smul (hB : IsCompletionLike A f B) (a : A) (b : B) :
    (redQuotEquiv hB).symm (Ideal.Quotient.mk _ (a • b)) =
      a • (redQuotEquiv hB).symm (Ideal.Quotient.mk _ b) := by
  apply (redQuotEquiv hB).injective
  rw [RingEquiv.apply_symm_apply,
    Algebra.smul_def a ((redQuotEquiv hB).symm (Ideal.Quotient.mk _ b)),
    map_mul, RingEquiv.apply_symm_apply, Ideal.Quotient.algebraMap_eq, redQuotEquiv_mk,
    ← map_mul, Algebra.smul_def]

/-- The `A`-linear "reduction" map `B → A/(f)`, inverse to `A/(f) ≅ B/fB`. -/
private noncomputable def redMap (hB : IsCompletionLike A f B) :
    B →ₗ[A] (A ⧸ Ideal.span {f}) where
  toFun b := (redQuotEquiv hB).symm (Ideal.Quotient.mk _ b)
  map_add' x y := by simp
  map_smul' a b := redQuotEquiv_symm_smul hB a b

private lemma redMap_one (hB : IsCompletionLike A f B) : redMap hB 1 = 1 := by
  simp [redMap]

/-- If `p ⊗ₜ 1` is divisible by `f` in `P ⊗ B`, then `p` is divisible by `f` in `P`. -/
private lemma exists_smul_of_tmul_one (hB : IsCompletionLike A f B)
    {P : Type u} [AddCommGroup P] [Module A P] (p : P) (w : P ⊗[A] B)
    (h : p ⊗ₜ[A] (1 : B) = f • w) : ∃ q : P, p = f • q := by
  have hz : ∀ y : P ⧸ (Ideal.span {f} • (⊤ : Submodule A P)), f • y = 0 := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H p =>
      rw [← Submodule.Quotient.mk_smul]
      exact (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) trivial)
  set T : P ⊗[A] B →ₗ[A] P ⧸ (Ideal.span {f} • (⊤ : Submodule A P)) :=
    (TensorProduct.tensorQuotEquivQuotSMul P (Ideal.span {f})).toLinearMap ∘ₗ
      LinearMap.lTensor P (redMap hB) with hT
  have he : redMap hB 1 = Ideal.Quotient.mk (Ideal.span {f}) 1 := by
    rw [redMap_one hB, map_one]
  have h1 : T (p ⊗ₜ[A] (1 : B)) = Submodule.Quotient.mk p := by
    rw [hT]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.lTensor_tmul,
      LinearEquiv.coe_coe, he, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk, one_smul]
  have h2 : T (f • w) = 0 := by rw [map_smul, hz]
  have h3 : (Submodule.Quotient.mk p : P ⧸ (Ideal.span {f} • (⊤ : Submodule A P))) = 0 := by
    rw [← h1, h, h2]
  rw [Submodule.Quotient.mk_eq_zero, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists] at h3
  obtain ⟨q, -, hq⟩ := h3
  exact ⟨q, hq.symm⟩

/-- `f` is regular on the base change of a free module. -/
private lemma isSMulRegular_finsupp_tensor (hBf : IsSMulRegular B f) (M : Type u) :
    IsSMulRegular ((M →₀ A) ⊗[A] B) f := by
  classical
  intro x y hxy
  set E := TensorProduct.finsuppScalarLeft A B M with hE
  apply E.injective
  have h2 : f • E x = f • E y := by
    rw [← LinearEquiv.map_smul, ← LinearEquiv.map_smul]
    exact congrArg E hxy
  ext i
  exact hBf (by simpa using congrArg (fun g : M →₀ B => g i) h2)

/-- Vanishing of the relevant `Tor`: if the image of `k : K ⊗ B` (where `K = ker φ`) in
`F ⊗ B` is divisible by `f`, then `k` itself is divisible by `f`. -/
private lemma exists_smul_of_rTensor_subtype {F M : Type u} [AddCommGroup F] [Module A F]
    [AddCommGroup M] [Module A M] (hB : IsCompletionLike A f B)
    (φ : F →ₗ[A] M) (hM : IsSMulRegular M f)
    (k : (LinearMap.ker φ) ⊗[A] B) (x : F ⊗[A] B)
    (h : LinearMap.rTensor B (LinearMap.ker φ).subtype k = f • x) :
    ∃ k' : (LinearMap.ker φ) ⊗[A] B, k = f • k' := by
  obtain ⟨a, k₁, hk⟩ := exists_tmul_one_add_smul hB k
  have hpush : LinearMap.rTensor B (LinearMap.ker φ).subtype k
      = (a : F) ⊗ₜ[A] (1 : B) + f • LinearMap.rTensor B (LinearMap.ker φ).subtype k₁ := by
    rw [hk, map_add, map_smul, LinearMap.rTensor_tmul]
    rfl
  have hdvd : (a : F) ⊗ₜ[A] (1 : B)
      = f • (x - LinearMap.rTensor B (LinearMap.ker φ).subtype k₁) := by
    rw [smul_sub, ← h, hpush]; abel
  obtain ⟨y, hy⟩ := exists_smul_of_tmul_one hB (a : F) _ hdvd
  have hy0 : φ y = 0 := by
    apply hM
    have hfy : φ (f • y) = 0 := by rw [← hy]; exact a.2
    simpa using hfy
  refine ⟨(⟨y, hy0⟩ : LinearMap.ker φ) ⊗ₜ[A] (1 : B) + k₁, ?_⟩
  rw [hk, smul_add, TensorProduct.smul_tmul']
  congr 2
  exact Subtype.ext (by simpa using hy)

end Aux

/-- The analytic heart of Beauville-Laszlo (Stacks 0BNI, cf. 0BNW): over a
completion-like pair with `f` regular on `A` and on `B`, `f`-regularity survives base
change: if `f` is regular on `M` then `f` is regular on `M ⊗ B`.  (False without the
completion-like hypothesis; this is exactly where BL differs from flat descent.) -/
theorem isSMulRegular_baseChange
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (hA : IsSMulRegular A f) (hBf : IsSMulRegular B f)
    (M : Type u) [AddCommGroup M] [Module A M] (hM : IsSMulRegular M f) :
    IsSMulRegular (M ⊗[A] B) f := by
  classical
  set φ : (M →₀ A) →ₗ[A] M := Finsupp.linearCombination A (id : M → M) with hphi
  have hφ : Function.Surjective φ := Finsupp.linearCombination_surjective A Function.surjective_id
  set ψ : (LinearMap.ker φ) ⊗[A] B →ₗ[A] (M →₀ A) ⊗[A] B :=
    LinearMap.rTensor B (LinearMap.ker φ).subtype with hψ
  set φ' : (M →₀ A) ⊗[A] B →ₗ[A] M ⊗[A] B := LinearMap.rTensor B φ with hφ'
  have hex : Function.Exact ψ φ' := rTensor_exact B (LinearMap.exact_subtype_ker_map φ) hφ
  have hsurj : Function.Surjective φ' := LinearMap.rTensor_surjective B hφ
  have hreg : IsSMulRegular ((M →₀ A) ⊗[A] B) f := isSMulRegular_finsupp_tensor hBf M
  have core : ∀ t : M ⊗[A] B, f • t = 0 → t = 0 := by
    intro t ht
    obtain ⟨x, hx⟩ := hsurj t
    have h0 : φ' (f • x) = 0 := by rw [map_smul, hx, ht]
    obtain ⟨k, hk⟩ := (hex (f • x)).mp h0
    obtain ⟨k', hk'⟩ := exists_smul_of_rTensor_subtype hB φ hM k x hk
    have hxe : x = ψ k' := by
      apply hreg
      show f • x = f • ψ k'
      rw [← hk, hk', map_smul]
    rw [← hx, hxe]
    exact hex.apply_apply_eq_zero k'
  intro y z hyz
  have h1 : f • (y - z) = 0 := by rw [smul_sub]; exact sub_eq_zero_of_eq hyz
  exact sub_eq_zero.mp (core _ h1)
/- ===== node D07 (D07_a2): verified by Aristotle ===== -/
section AdicHelpers

variable {A : Type u} [CommRing A]

/-- Membership in `(span {f})^j • ⊤` (as a submodule of `A` itself) means divisibility
by `f ^ j`. -/
private lemma mem_pow_span_smul_top_iff (f : A) (j : ℕ) (x : A) :
    x ∈ (Ideal.span {f} ^ j • ⊤ : Submodule A A) ↔ ∃ b, x = f ^ j * b := by
  rw [show (Ideal.span {f} ^ j • ⊤ : Submodule A A) = (Ideal.span {f} ^ j : Ideal A) by
      ext y; simp, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  exact ⟨fun ⟨b, hb⟩ => ⟨b, by rw [← hb]; ring⟩, fun ⟨b, hb⟩ => ⟨b, by rw [hb]; ring⟩⟩

/-- The sequence-level construction behind Stacks Tag 0BNJ: if `a` is a sequence whose
consecutive differences are divisible by the corresponding powers of `f`, and `a n` is
divisible by `f ^ n`, then there is a sequence `y` with `f ^ n * y k = a (n + k)` whose
consecutive differences are divisible by the corresponding powers of `f`. -/
private lemma exists_seq_div_pow (f : A) (n : ℕ) (a : ℕ → A)
    (hstep : ∀ j, ∃ b, a (j + 1) - a j = f ^ j * b)
    (h0 : ∃ c, a n = f ^ n * c) :
    ∃ y : ℕ → A, (∀ k, f ^ n * y k = a (n + k)) ∧ ∀ k, ∃ d, y (k + 1) - y k = f ^ k * d := by
  choose b hb using hstep
  obtain ⟨c, hc⟩ := h0
  refine ⟨fun k => Nat.rec c (fun k yk => yk + f ^ k * b (n + k)) k, ?_, ?_⟩
  · intro k
    induction k with
    | zero => simpa using hc.symm
    | succ k ih =>
      show f ^ n * (_ + f ^ k * b (n + k)) = a (n + (k + 1))
      rw [mul_add, ih]
      have h2 : f ^ n * (f ^ k * b (n + k)) = a (n + k + 1) - a (n + k) := by
        rw [hb (n + k)]; ring
      rw [h2, show n + (k + 1) = n + k + 1 from rfl]
      ring
  · intro k
    exact ⟨b (n + k), by simp⟩

/-- Hard direction of the kernel computation: an element of the `f`-adic completion whose
`n`-th component vanishes is divisible by `f ^ n`. -/
private lemma exists_mul_of_val_eq_zero (f : A) (n : ℕ)
    (x : AdicCompletion (Ideal.span {f}) A) (hx : x.val n = 0) :
    ∃ y : AdicCompletion (Ideal.span {f}) A,
      x = algebraMap A (AdicCompletion (Ideal.span {f}) A) (f ^ n) * y := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective (Ideal.span {f}) A x
  have h0 : ∃ c, a n = f ^ n * c := by
    rw [← mem_pow_span_smul_top_iff]
    have h : (Submodule.Quotient.mk (a n) : A ⧸ (Ideal.span {f} ^ n • ⊤ : Submodule A A)) = 0 := hx
    rwa [Submodule.Quotient.mk_eq_zero] at h
  have hstep : ∀ j, ∃ b, a (j + 1) - a j = f ^ j * b := by
    intro j
    rw [← mem_pow_span_smul_top_iff]
    have h := a.property (Nat.le_succ j)
    rw [SModEq.sub_mem] at h
    simpa using (Submodule.neg_mem _ h)
  obtain ⟨y, hy1, hy2⟩ := exists_seq_div_pow f n a.val hstep h0
  have hcauchy : ∀ k, y k ≡ y (k + 1) [SMOD (Ideal.span {f} ^ k • ⊤ : Submodule A A)] := by
    intro k
    rw [SModEq.sub_mem, mem_pow_span_smul_top_iff]
    obtain ⟨d, hd⟩ := hy2 k
    exact ⟨-d, by rw [← neg_sub (y (k + 1)) (y k), hd]; ring⟩
  refine ⟨AdicCompletion.mk (Ideal.span {f}) A
    (AdicCompletion.AdicCauchySequence.mk (Ideal.span {f}) A y hcauchy), ?_⟩
  ext k
  show (Submodule.Quotient.mk (a k) : A ⧸ (Ideal.span {f} ^ k • ⊤ : Submodule A A))
      = Submodule.Quotient.mk (f ^ n * y k)
  rw [hy1 k]
  exact a.property (Nat.le_add_left k n)

/-- Easy direction: a multiple of `f ^ n` in the completion has vanishing `n`-th component. -/
private lemma val_eq_zero_of_mul (f : A) (n : ℕ)
    (y : AdicCompletion (Ideal.span {f}) A) :
    (algebraMap A (AdicCompletion (Ideal.span {f}) A) (f ^ n) * y).val n = 0 := by
  show (Submodule.Quotient.mk (f ^ n) : A ⧸ (Ideal.span {f} ^ n • ⊤ : Submodule A A)) * y.val n = 0
  have h : (Submodule.Quotient.mk (f ^ n) : A ⧸ (Ideal.span {f} ^ n • ⊤ : Submodule A A)) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero, mem_pow_span_smul_top_iff]
    exact ⟨1, by ring⟩
  rw [h, zero_mul]

/-- The ideal `f^n Â` of the `f`-adic completion is exactly the kernel of the `n`-th
component map. -/
private lemma mem_map_span_iff (f : A) (n : ℕ)
    (x : AdicCompletion (Ideal.span {f}) A) :
    x ∈ (Ideal.span {f ^ n}).map (algebraMap A (AdicCompletion (Ideal.span {f}) A)) ↔
      x.val n = 0 := by
  constructor
  · intro hx
    rw [Ideal.map_span, Set.image_singleton] at hx
    rw [Ideal.mem_span_singleton] at hx
    obtain ⟨b, rfl⟩ := hx
    exact val_eq_zero_of_mul f n b
  · intro hx
    obtain ⟨y, rfl⟩ := exists_mul_of_val_eq_zero f n x hx
    rw [Ideal.map_span, Set.image_singleton]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end AdicHelpers

/-- Stacks Tag 0BNJ: for any commutative ring `A` and `f : A`, the `f`-adic completion
satisfies the completion-like property: `A/f^n → Â/f^nÂ` is bijective for `n ≥ 1`. -/
theorem isCompletionLike_adicCompletion
    (A : Type u) [CommRing A] (f : A) :
    IsCompletionLike A f (AdicCompletion (Ideal.span {f}) A) := by
  constructor
  · intro n _ z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective
      (Ideal.span {f} ^ n • ⊤ : Submodule A A) (b.val n)
    refine ⟨c, ?_⟩
    show Ideal.Quotient.mk _ (algebraMap A (AdicCompletion (Ideal.span {f}) A) c) = _
    rw [Ideal.Quotient.eq, mem_map_span_iff]
    show (Submodule.Quotient.mk c : A ⧸ (Ideal.span {f} ^ n • ⊤ : Submodule A A)) - b.val n = 0
    rw [hc, sub_self]
  · intro n _
    ext x
    rw [RingHom.mem_ker]
    show Ideal.Quotient.mk _ (algebraMap A (AdicCompletion (Ideal.span {f}) A) x) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, mem_map_span_iff]
    show (Submodule.Quotient.mk x : A ⧸ (Ideal.span {f} ^ n • ⊤ : Submodule A A)) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, mem_pow_span_smul_top_iff, Ideal.mem_span_singleton']
    exact ⟨fun ⟨b, hb⟩ => ⟨b, by rw [hb]; ring⟩, fun ⟨b, hb⟩ => ⟨b, by rw [← hb]; ring⟩⟩
/- ===== node D08 (D08_a1): verified by Aristotle ===== -/
private lemma mem_span_pow_of_mul_mem_span_succ
    (A : Type u) [CommRing A] (f a : A) (hA : IsSMulRegular A f) (n : ℕ)
    (h : f * a ∈ Ideal.span {f ^ (n + 1)}) : a ∈ Ideal.span {f ^ n} := by
  rw [Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  apply hA
  simp only [smul_eq_mul]
  calc
    f * a = f ^ (n + 1) * c := hc
    _ = f * (f ^ n * c) := by rw [pow_succ]; ring

/-- If `f` is a non-zerodivisor on `A`, it is a non-zerodivisor on the `f`-adic
completion of `A` (Stacks 0BNI region, cf. 0BNS remark). -/
theorem isSMulRegular_adicCompletion
    (A : Type u) [CommRing A] (f : A) (hA : IsSMulRegular A f) :
    IsSMulRegular (AdicCompletion (Ideal.span {f}) A) f := by
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro x hx
  apply AdicCompletion.ext
  intro n
  obtain ⟨a, ha⟩ := Quotient.mk_surjective (x.val (n + 1))
  have hfa0 : f * a ∈ (Ideal.span {f}) ^ (n + 1) • (⊤ : Submodule A A) := by
    rw [← Submodule.Quotient.mk_eq_zero]
    rw [show f * a = f • a from (smul_eq_mul f a).symm, Submodule.Quotient.mk_smul]
    calc
      f • Submodule.Quotient.mk a = f • x.val (n + 1) := congrArg (f • ·) ha
      _ = (f • x).val (n + 1) := (AdicCompletion.val_smul_apply f x (n + 1)).symm
      _ = 0 := congrArg (fun z : AdicCompletion (Ideal.span {f}) A => z.val (n + 1)) hx
  have hfa : f * a ∈ Ideal.span {f ^ (n + 1)} := by
    simpa only [Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top] using hfa0
  have ha' : a ∈ Ideal.span {f ^ n} :=
    mem_span_pow_of_mul_mem_span_succ A f a hA n hfa
  rw [← x.property (Nat.le_succ n), ← ha]
  change AdicCompletion.transitionMap (Ideal.span {f}) A (Nat.le_succ n)
      (Submodule.Quotient.mk a) = 0
  rw [show AdicCompletion.transitionMap (Ideal.span {f}) A (Nat.le_succ n)
      (Submodule.Quotient.mk a) = Submodule.Quotient.mk a from rfl]
  rw [Submodule.Quotient.mk_eq_zero, Ideal.span_singleton_pow]
  simpa only [smul_eq_mul, Ideal.mul_top] using ha'
/- ===== node D10 (D10_a1): verified by Aristotle ===== -/
/-- The first projection exhibits `(Fin n → Rf)` as the localization of the glued
module at the powers of `f`. -/
theorem gluedFst_isLocalizedModule
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (hA : IsSMulRegular A f) (hBf : IsSMulRegular B f)
    (Rf : Type u) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    [IsLocalization.Away (algebraMap A B f) Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    IsLocalizedModule (Submonoid.powers f) (gluedFst A B Rf Bf ρ n g) := by
  let rmap : (Fin n → A) →ₗ[A] (Fin n → Rf) :=
    (Algebra.linearMap A Rf).compLeft (Fin n)
  let bmapB : (Fin n → B) →ₗ[B] (Fin n → Bf) :=
    (Algebra.linearMap B Bf).compLeft (Fin n)
  let bmap : (Fin n → B) →ₗ[A] (Fin n → Bf) := bmapB.restrictScalars A
  let rpi : (Fin n → A) →ₗ[A] (Fin n → Rf) :=
    LinearMap.pi (fun i : Fin n ↦ (Algebra.linearMap A Rf).comp (LinearMap.proj i))
  haveI hrpi : IsLocalizedModule (Submonoid.powers f) rpi :=
    IsLocalizedModule.pi (Submonoid.powers f) (fun _ : Fin n ↦ Algebra.linearMap A Rf)
  have hr : IsLocalizedModule (Submonoid.powers f) rmap := by
    have he : rpi = rmap := by ext x i; rfl
    rw [← he]
    infer_instance
  let bpi : (Fin n → B) →ₗ[B] (Fin n → Bf) :=
    LinearMap.pi (fun i : Fin n ↦ (Algebra.linearMap B Bf).comp (LinearMap.proj i))
  haveI hbpi : IsLocalizedModule (Submonoid.powers (algebraMap A B f)) bpi :=
    IsLocalizedModule.pi (Submonoid.powers (algebraMap A B f))
      (fun _ : Fin n ↦ Algebra.linearMap B Bf)
  have hb : IsLocalizedModule (Submonoid.powers (algebraMap A B f)) bmapB := by
    have he : bpi = bmapB := by ext x i; rfl
    rw [← he]
    infer_instance
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · exact hr.map_units
  · intro z
    let w : Fin n → Bf := g (fun i ↦ ρ (z i))
    obtain ⟨⟨b, s⟩, hs⟩ := hb.surj w
    obtain ⟨k, hk⟩ := s.property
    let t : Submonoid.powers f := ⟨f ^ k, ⟨k, rfl⟩⟩
    have hs' : (fun i ↦ algebraMap A B f ^ k • w i) = bmapB b := by
      simpa only [Submonoid.smul_def, ← hk] using hs
    let p : (Fin n → Rf) × (Fin n → B) := (t • z, b)
    have hp : p ∈ gluedModule A B Rf Bf ρ n g := by
      change glueDelta A B Rf Bf ρ n g p = 0
      ext i
      change g (fun i ↦ ρ ((t : A) • z i)) i - algebraMap B Bf (b i) = 0
      change g (fun i ↦ ρ ((f ^ k) • z i)) i - algebraMap B Bf (b i) = 0
      have heq : (fun i ↦ ρ ((f ^ k) • z i)) = (f ^ k) • (fun i ↦ ρ (z i)) := by
        ext j
        simp
      rw [heq]
      have hg := g.map_smul_of_tower (f ^ k) (fun i ↦ ρ (z i))
      have hgi : g ((f ^ k) • (fun i ↦ ρ (z i))) i =
          ((f ^ k) • g (fun i ↦ ρ (z i))) i := by
        exact congr_fun hg i
      rw [hgi]
      simp only [Pi.smul_apply, Algebra.smul_def]
      rw [show algebraMap A Bf (f ^ k) =
        algebraMap B Bf (algebraMap A B (f ^ k)) from
          (IsScalarTower.algebraMap_apply A B Bf (f ^ k))]
      have hi := congr_fun hs' i
      have hi' : algebraMap B Bf (algebraMap A B f ^ k) * w i =
          algebraMap B Bf (b i) := by
        simpa only [Pi.smul_apply, Algebra.smul_def] using hi
      simpa [w] using sub_eq_zero.mpr hi'
    refine ⟨⟨⟨p, hp⟩, t⟩, ?_⟩
    rfl
  · intro x y hxy
    refine ⟨1, ?_⟩
    simp only [one_smul]
    apply Subtype.ext
    apply Prod.ext hxy
    have hker : Function.Injective bmapB := by
      rw [hb.injective_iff_isRegular]
      intro s
      rcases s.property with ⟨k, hk⟩
      intro a b hab
      apply funext
      intro i
      have hi := congr_fun hab i
      apply hBf.pow k
      simpa only [Submonoid.smul_def, ← hk, Algebra.smul_def, map_pow] using hi
    apply hker
    change x.val.1 = y.val.1 at hxy
    have hx := x.property
    have hy := y.property
    change glueDelta A B Rf Bf ρ n g x.val = 0 at hx
    change glueDelta A B Rf Bf ρ n g y.val = 0 at hy
    ext i
    have ex := congr_fun (show g (fun i ↦ ρ (x.val.1 i)) - bmapB x.val.2 = 0 by exact hx) i
    have ey := congr_fun (show g (fun i ↦ ρ (y.val.1 i)) - bmapB y.val.2 = 0 by exact hy) i
    dsimp at ex ey ⊢
    rw [hxy] at ex
    exact (sub_eq_zero.mp ex).symm.trans (sub_eq_zero.mp ey)
/- ===== node D11 (D11_a2): verified by Aristotle ===== -/
/-! ### Auxiliary development

We prove the theorem following Stacks Tag 0BP2, specialised to the case of a free glueing
datum.  Write `ι = algebraMap B Bf` and `N = gluedModule`.  The two key inputs are:

* *density*: `Bf = ρ (Rf) + ι (B)` (Stacks 0BNR(1)); together with
* *the arithmetic square*: if `ρ x = ι y` then `x` and `y` come from a common `a : A`
  (`scalar_pullback_exists`).

Surjectivity of the base change map is proved by an explicit computation.  Injectivity is
obtained by a diagram chase through the auxiliary fibre product

`P = {(x, y, b) : g (ρ ∘ x) - ρ ∘ y = ι ∘ b} ⊆ (Fin n → Rf) × (Fin n → Rf) × (Fin n → B)`,

which sits in two exact sequences `0 → N → P → (Fin n → Rf) → 0` (whose quotient is
`A`-flat) and `(Fin n → A) → P → (Fin n → Rf) → 0`.

The hypothesis that `f` is a nonzerodivisor on `A` turns out not to be needed: only
regularity of `f` on `B` and the completion-like hypothesis are used.
-/

section Aux

variable {A : Type u} [CommRing A] {f : A}
  {B : Type u} [CommRing B] [Algebra A B]
  {Rf : Type u} [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf]
  {Bf : Type u} [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
  [IsLocalization.Away (algebraMap A B f) Bf]
  {ρ : Rf →ₐ[A] Bf} {n : ℕ} {g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)}

/-- `A → Bf` factors through `B`. -/
private lemma bl_algebraMap_eq (a : A) :
    algebraMap A Bf a = algebraMap B Bf (algebraMap A B a) :=
  IsScalarTower.algebraMap_apply A B Bf a

omit [Algebra A Bf] [IsScalarTower A B Bf] in
/-- `B → Bf` is injective since `f` is a nonzerodivisor on `B`. -/
private lemma bl_iota_injective (hBf : IsSMulRegular B f) :
    Function.Injective (algebraMap B Bf) := by
  have hf : algebraMap A B f ∈ nonZeroDivisors B := by
    rw [mem_nonZeroDivisors_iff_right]
    intro b hb
    exact hBf (by simpa [Algebra.smul_def, mul_comm] using hb)
  exact IsLocalization.injective Bf (Submonoid.powers_le.2 hf)

/-- `f` becomes invertible in `Bf`. -/
private lemma bl_isUnit_f (B : Type u) [CommRing B] [Algebra A B] [Algebra B Bf]
    [IsScalarTower A B Bf] [IsLocalization.Away (algebraMap A B f) Bf] :
    IsUnit (algebraMap A Bf f) := by
  have h : IsUnit (algebraMap B Bf (algebraMap A B f)) :=
    IsLocalization.map_units Bf
      (⟨algebraMap A B f, Submonoid.mem_powers _⟩ : Submonoid.powers (algebraMap A B f))
  rwa [← bl_algebraMap_eq] at h

/-- Common denominators for a finite family of elements of `Bf`. -/
private lemma bl_exists_denom {ι : Type} [Fintype ι] (v : ι → Bf) :
    ∃ (k : ℕ) (c : ι → B), ∀ i, (algebraMap A Bf f) ^ k * v i = algebraMap B Bf (c i) := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples
    (Submonoid.powers (algebraMap A B f)) (Finset.univ : Finset ι) v
  obtain ⟨k, hk⟩ := b.2
  have hb' : ∀ i, ∃ c : B, algebraMap B Bf c = (b : B) • v i := fun i => hb i (Finset.mem_univ i)
  choose c hc using hb'
  refine ⟨k, c, fun i => ?_⟩
  rw [hc i, Algebra.smul_def, ← hk, map_pow, ← bl_algebraMap_eq (A := A) (B := B) (Bf := Bf)]

/-- Every element of `B` is congruent to an element of `A` modulo `f ^ k`. -/
private lemma bl_mod_pow (hB : IsCompletionLike A f B) (k : ℕ) (b : B) :
    ∃ (a : A) (c : B), b = algebraMap A B a + (algebraMap A B f) ^ k * c := by
  by_cases hk : 0 < k
  · -- k > 0 case: use the IsCompletionLike hypothesis
    let q := (Ideal.span {f ^ k}).map (algebraMap A B)
    have hsurj := hB.surjective_mod k hk
    let π : B →+* B ⧸ q := Ideal.Quotient.mk q
    obtain ⟨a, ha⟩ := hsurj (π b)
    have hdiff : b - algebraMap A B a ∈ q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      exact ha.symm
    -- q is generated by (algebraMap A B f)^k
    have hq : q = Ideal.span {(algebraMap A B f) ^ k} := by
      show Ideal.map (algebraMap A B) (Ideal.span {f ^ k}) = Ideal.span {(algebraMap A B f) ^ k}
      rw [Ideal.map_span]
      simp [Set.image_singleton, ← map_pow]
    rw [hq] at hdiff
    rw [Ideal.mem_span_singleton] at hdiff
    obtain ⟨c, hc⟩ := hdiff
    exact ⟨a, c, by rw [← hc]; ring⟩
  · -- k = 0 case: f^0 = 1, so everything is divisible
    push_neg at hk
    rw [Nat.le_zero] at hk
    rw [hk, pow_zero]
    use 0, b
    simp

/-- Componentwise version of `bl_mod_pow`. -/
private lemma bl_mod_pow_fin (hB : IsCompletionLike A f B) (k : ℕ) {ι : Type} (b : ι → B) :
    ∃ (a : ι → A) (c : ι → B),
      ∀ i, b i = algebraMap A B (a i) + (algebraMap A B f) ^ k * c i := by
  choose a c hac using fun i => bl_mod_pow hB k (b i)
  exact ⟨a, c, hac⟩

/-- The image under `ρ` of `a / f ^ k`. -/
private lemma bl_rho_mk' (ρ : Rf →ₐ[A] Bf) (a : A) (k : ℕ) :
    (algebraMap A Bf f) ^ k *
        ρ (IsLocalization.mk' Rf a (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f)) =
      algebraMap A Bf a := by
  have h := IsLocalization.mk'_spec' Rf a (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f)
  calc (algebraMap A Bf f) ^ k *
        ρ (IsLocalization.mk' Rf a (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f))
      = ρ (algebraMap A Rf (f ^ k) *
          IsLocalization.mk' Rf a (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f)) := by
        rw [map_mul, ρ.commutes, map_pow]
    _ = ρ (algebraMap A Rf a) := by rw [h]
    _ = algebraMap A Bf a := ρ.commutes a

/-- Density: `Bf = ρ (Rf) + algebraMap B Bf (B)`, componentwise for a finite family. -/
private lemma bl_density (hB : IsCompletionLike A f B) (ρ : Rf →ₐ[A] Bf)
    {ι : Type} [Fintype ι] (v : ι → Bf) :
    ∃ (x : ι → Rf) (b : ι → B), ∀ i, v i = ρ (x i) + algebraMap B Bf (b i) := by
  obtain ⟨k, c, hc⟩ := bl_exists_denom (A := A) (f := f) (B := B) v
  obtain ⟨a, c', hac⟩ := bl_mod_pow_fin hB k c
  refine ⟨fun i => IsLocalization.mk' Rf (a i) (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f), c',
    fun i => ?_⟩
  have hunit : IsUnit ((algebraMap A Bf f) ^ k) := (bl_isUnit_f (Bf := Bf) B).pow k
  refine hunit.mul_left_cancel ?_
  rw [hc i, hac i, mul_add, bl_rho_mk' ρ (a i) k, map_add, map_mul, map_pow,
    ← bl_algebraMap_eq (A := A) (B := B) (Bf := Bf) (a i),
    ← bl_algebraMap_eq (A := A) (B := B) (Bf := Bf) f]

/-- The arithmetic square: `A = Rf ×_{Bf} B`.  This is the module glueing square of
Stacks Tag 0BP2 for the module `M = A`. -/
private lemma scalar_pullback_exists (hB : IsCompletionLike A f B) (hBf : IsSMulRegular B f)
    (ρ : Rf →ₐ[A] Bf) (x : Rf) (y : B) (hxy : ρ x = algebraMap B Bf y) :
    ∃ a : A, algebraMap A Rf a = x ∧ algebraMap A B a = y := by
  obtain ⟨⟨a₀, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) x
  obtain ⟨k, hk⟩ := m.2
  have hm : m = (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hk.symm
  subst hm
  have h1 : (algebraMap A Bf f) ^ k *
      ρ (IsLocalization.mk' Rf a₀ (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f)) =
      algebraMap A Bf a₀ := bl_rho_mk' ρ a₀ k
  rw [hxy] at h1
  have h2 : algebraMap B Bf ((algebraMap A B f) ^ k * y) =
      algebraMap B Bf (algebraMap A B a₀) := by
    rw [map_mul, map_pow, ← bl_algebraMap_eq (A := A) (B := B) (Bf := Bf),
      ← bl_algebraMap_eq (A := A) (B := B) (Bf := Bf)]
    exact h1
  have h3 : (algebraMap A B f) ^ k * y = algebraMap A B a₀ := bl_iota_injective hBf h2
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    refine ⟨a₀, ?_, ?_⟩
    · rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul]
      simp
    · simpa using h3.symm
  · have hker : a₀ ∈ RingHom.ker
        (algebraMap A (B ⧸ (Ideal.span {f ^ k}).map (algebraMap A B))) := by
      rw [RingHom.mem_ker]
      have hq : algebraMap A (B ⧸ (Ideal.span {f ^ k}).map (algebraMap A B)) a₀ =
          Ideal.Quotient.mk ((Ideal.span {f ^ k}).map (algebraMap A B)) (algebraMap A B a₀) := by
        rw [IsScalarTower.algebraMap_apply A B (B ⧸ (Ideal.span {f ^ k}).map (algebraMap A B))]
        rfl
      rw [hq, ← h3, Ideal.Quotient.eq_zero_iff_mem]
      have hmem : (algebraMap A B f) ^ k ∈ (Ideal.span {f ^ k}).map (algebraMap A B) := by
        rw [← map_pow]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
      exact Ideal.mul_mem_right _ _ hmem
    rw [hB.ker_mod k hkpos, Ideal.mem_span_singleton] at hker
    obtain ⟨a, ha⟩ := hker
    refine ⟨a, ?_, ?_⟩
    · rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ha, map_mul]
      ring
    · refine (hBf.pow k) ?_
      show f ^ k • algebraMap A B a = f ^ k • y
      rw [Algebra.smul_def, Algebra.smul_def, map_pow, h3, ha, map_mul, map_pow]

/-- A uniform denominator bound for the matrix of `g`. -/
private lemma bl_g_denom (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    ∃ (k : ℕ) (d : Fin n → Fin n → B), ∀ j i,
      (algebraMap A Bf f) ^ k * g (Pi.single j 1) i = algebraMap B Bf (d j i) := by
  obtain ⟨k, c, hc⟩ :=
    bl_exists_denom (A := A) (f := f) (B := B)
      (fun p : Fin n × Fin n => g (Pi.single p.1 1) p.2)
  exact ⟨k, fun j i => c (j, i), fun j i => hc (j, i)⟩

omit [Algebra A B] [IsScalarTower A B Bf] [IsLocalization.Away (algebraMap A B f) Bf] in
/-- The denominator bound of `bl_g_denom`, applied to an integral vector. -/
private lemma bl_g_denom_apply (k : ℕ) (d : Fin n → Fin n → B)
    (hd : ∀ j i, (algebraMap A Bf f) ^ k * g (Pi.single j 1) i = algebraMap B Bf (d j i))
    (c : Fin n → B) (i : Fin n) :
    (algebraMap A Bf f) ^ k * g (fun j => algebraMap B Bf (c j)) i =
      algebraMap B Bf ((∑ j, c j • d j) i) := by
  have hdecomp : (fun j => algebraMap B Bf (c j)) =
      ∑ j, (algebraMap B Bf (c j)) • (Pi.single j 1 : Fin n → Bf) := by
    funext l
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
  rw [hdecomp, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, mul_comm ((algebraMap A Bf f) ^ k) (algebraMap B Bf (c j)), mul_assoc,
    hd j i, ← map_mul]

/-- Surjectivity of the map `(Fin n → Rf) → (Fin n → Bf) / (Fin n → B)` induced by `g ∘ ρ`
(Stacks Tag 0BP2, first paragraph of the proof of the theorem).  The correction term is
explicitly a `B`-combination of the vectors `d j` produced by `bl_g_denom`. -/
private lemma bl_q_surj (hB : IsCompletionLike A f B) (k : ℕ) (d : Fin n → Fin n → B)
    (hd : ∀ j i, (algebraMap A Bf f) ^ k * g (Pi.single j 1) i = algebraMap B Bf (d j i))
    (v : Fin n → Bf) :
    ∃ (x : Fin n → Rf) (c : Fin n → B), ∀ i,
      g (fun j => ρ (x j)) i = v i - algebraMap B Bf ((∑ j, c j • d j) i) := by
  obtain ⟨m, c, hc⟩ := bl_exists_denom (A := A) (f := f) (B := B) (fun i => g.symm v i)
  obtain ⟨a, c', hac⟩ := bl_mod_pow_fin hB (m + k) c
  refine ⟨fun i => IsLocalization.mk' Rf (a i) (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f), c',
    fun i => ?_⟩
  have hunit : IsUnit ((algebraMap A Bf f) ^ m) := (bl_isUnit_f (Bf := Bf) B).pow m
  refine hunit.mul_left_cancel ?_
  -- the left hand side
  have hL : (algebraMap A Bf f) ^ m *
      g (fun j => ρ (IsLocalization.mk' Rf (a j)
        (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f))) i
      = g (fun j => algebraMap A Bf (a j)) i := by
    have : ((algebraMap A Bf f) ^ m) • (fun j => ρ (IsLocalization.mk' Rf (a j)
        (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f))) = (fun j => algebraMap A Bf (a j)) := by
      funext j
      simpa [smul_eq_mul] using bl_rho_mk' ρ (a j) m
    rw [← this, map_smul]
    simp [smul_eq_mul]
  rw [hL]
  -- the vector identity
  have key : (fun j => algebraMap A Bf (a j)) =
      ((algebraMap A Bf f) ^ m) • (fun j => g.symm v j) -
        ((algebraMap A Bf f) ^ (m + k)) • (fun j => algebraMap B Bf (c' j)) := by
    funext j
    have h1 := hc j
    rw [hac j, map_add, map_mul, map_pow, ← bl_algebraMap_eq (A := A) (B := B) (Bf := Bf),
      ← bl_algebraMap_eq (A := A) (B := B) (Bf := Bf)] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1]
    ring
  rw [key, map_sub, map_smul, map_smul]
  have hgv : g (fun j => g.symm v j) = v := by
    have : (fun j => g.symm v j) = g.symm v := rfl
    rw [this, LinearEquiv.apply_symm_apply]
  rw [hgv]
  have hdd : (algebraMap A Bf f) ^ k * g (fun j => algebraMap B Bf (c' j)) i =
      algebraMap B Bf ((∑ j, c' j • d j) i) := bl_g_denom_apply k d hd c' i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [pow_add, mul_assoc, hdd, mul_sub]

private lemma bl_q_surj' (hB : IsCompletionLike A f B) (v : Fin n → Bf) :
    ∃ (x : Fin n → Rf) (b : Fin n → B), ∀ i,
      g (fun j => ρ (x j)) i = v i + algebraMap B Bf (b i) := by
  obtain ⟨k, d, hd⟩ := bl_g_denom (f := f) (B := B) n g
  obtain ⟨x, c, hx⟩ := bl_q_surj (ρ := ρ) hB k d hd v
  exact ⟨x, fun i => -((∑ j, c j • d j) i), fun i => by rw [hx i]; simp [sub_eq_add_neg]⟩

/-! #### The glued module -/

private lemma bl_mem_gluedModule (v : (Fin n → Rf) × (Fin n → B)) :
    v ∈ gluedModule A B Rf Bf ρ n g ↔
      ∀ i, g (fun j => ρ (v.1 j)) i = algebraMap B Bf (v.2 i) := by
  simp [gluedModule, glueDelta, LinearMap.mem_ker, funext_iff, sub_eq_zero,
    LinearMap.compLeft, Function.comp_def]

private lemma bl_gluedSnd_apply (t : ↥(gluedModule A B Rf Bf ρ n g)) :
    gluedSnd A B Rf Bf ρ n g t = (t : (Fin n → Rf) × (Fin n → B)).2 := rfl

private lemma bl_gluedFst_apply (t : ↥(gluedModule A B Rf Bf ρ n g)) :
    gluedFst A B Rf Bf ρ n g t = (t : (Fin n → Rf) × (Fin n → B)).1 := rfl

/-! #### Surjectivity -/

omit [IsLocalization.Away f Rf] [IsLocalization.Away (algebraMap A B f) Bf] in
/-- The `n` "basis" elements of the glued module coming from the denominator bound. -/
private lemma bl_glued_basis_elt (k : ℕ) (d : Fin n → Fin n → B)
    (hd : ∀ j i, (algebraMap A Bf f) ^ k * g (Pi.single j 1) i = algebraMap B Bf (d j i))
    (j : Fin n) :
    ((Pi.single j ((algebraMap A Rf f) ^ k) : Fin n → Rf), d j) ∈
      gluedModule A B Rf Bf ρ n g := by
  rw [bl_mem_gluedModule]
  intro i
  simp only [Pi.single_apply]
  have h1 : (fun j_1 => ρ (if j_1 = j then (algebraMap A Rf) f ^ k else 0)) =
      Pi.single j (ρ ((algebraMap A Rf) f ^ k)) := by
    ext j_1
    simp only [Pi.single_apply]
    by_cases hj : j_1 = j <;> simp [hj, map_zero]
  rw [h1]
  -- Now we have: g (Pi.single j (ρ ((algebraMap A Rf) f ^ k))) i = (algebraMap B Bf) (d j i)
  -- Use that ρ is an A-algebra map: ρ ((algebraMap A Rf) f) = (algebraMap A Bf) f
  have h2 : ρ ((algebraMap A Rf) f ^ k) = (algebraMap A Bf) f ^ k := by
    rw [map_pow]
    congr 1
    exact AlgHom.commutes ρ _
  rw [h2]
  -- Use Bf-linearity: g (Pi.single j c) = c • g (Pi.single j 1)
  have h3 : g (Pi.single j ((algebraMap A Bf) f ^ k)) = ((algebraMap A Bf) f ^ k) • g (Pi.single j 1) := by
    let e : Fin n → Bf := Pi.single j 1
    have heq : Pi.single j ((algebraMap A Bf) f ^ k) = ((algebraMap A Bf) f ^ k) • e := by
      ext i
      simp [Pi.smul_apply, Pi.single_apply, e]
    rw [heq]
    exact g.map_smul _ _
  rw [h3]
  simp only [Pi.smul_apply, smul_eq_mul]
  exact hd j i

/-- The main construction for surjectivity: every `y` is, modulo the `B`-span of the
elements produced by `bl_glued_basis_elt`, in the image of the glued module. -/
private lemma bl_glued_elt (hB : IsCompletionLike A f B) (k : ℕ) (d : Fin n → Fin n → B)
    (hd : ∀ j i, (algebraMap A Bf f) ^ k * g (Pi.single j 1) i = algebraMap B Bf (d j i))
    (y : Fin n → B) :
    ∃ (x : Fin n → Rf) (c : Fin n → B),
      (x, y - ∑ j, c j • d j) ∈ gluedModule A B Rf Bf ρ n g := by
  obtain ⟨x, c, hx⟩ := bl_q_surj (ρ := ρ) hB k d hd (fun i => algebraMap B Bf (y i))
  refine ⟨x, c, ?_⟩
  rw [bl_mem_gluedModule]
  intro i
  simpa using hx i

private lemma bl_span_eq_top (hB : IsCompletionLike A f B) :
    Submodule.span B (Set.range ⇑(gluedSnd A B Rf Bf ρ n g)) = ⊤ := by
  obtain ⟨k, d, hd⟩ := bl_g_denom (f := f) (B := B) n g
  rw [eq_top_iff]
  rintro y -
  obtain ⟨x, c, hx⟩ := bl_glued_elt (ρ := ρ) hB k d hd y
  have hmem : ∀ j, d j ∈ Submodule.span B (Set.range ⇑(gluedSnd A B Rf Bf ρ n g)) := fun j =>
    Submodule.subset_span ⟨⟨_, bl_glued_basis_elt (ρ := ρ) k d hd j⟩, rfl⟩
  have h1 : (y - ∑ j, c j • d j) ∈ Submodule.span B (Set.range ⇑(gluedSnd A B Rf Bf ρ n g)) :=
    Submodule.subset_span ⟨⟨_, hx⟩, rfl⟩
  have h2 : (∑ j, c j • d j) ∈ Submodule.span B (Set.range ⇑(gluedSnd A B Rf Bf ρ n g)) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmem j)
  simpa using Submodule.add_mem _ h1 h2

/-! #### The auxiliary fibre product -/

/-- `ι = algebraMap B Bf`, componentwise. -/
private noncomputable def blIotaPi (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (n : ℕ) : (Fin n → B) →ₗ[A] (Fin n → Bf) :=
  ((IsScalarTower.toAlgHom A B Bf).toLinearMap).compLeft (Fin n)

private lemma blIotaPi_apply (v : Fin n → B) (i : Fin n) :
    blIotaPi A B Bf n v i = algebraMap B Bf (v i) := rfl

/-- The defect map of the auxiliary fibre product `P`. -/
private noncomputable def blPbDelta (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    ((Fin n → Rf) × (Fin n → Rf) × (Fin n → B)) →ₗ[A] (Fin n → Bf) :=
  ((g.toLinearMap.restrictScalars A).comp
      ((ρ.toLinearMap.compLeft (Fin n)).comp
        (LinearMap.fst A (Fin n → Rf) ((Fin n → Rf) × (Fin n → B))))) -
    ((ρ.toLinearMap.compLeft (Fin n)).comp
      ((LinearMap.fst A (Fin n → Rf) (Fin n → B)).comp
        (LinearMap.snd A (Fin n → Rf) ((Fin n → Rf) × (Fin n → B))))) -
    ((blIotaPi A B Bf n).comp
      ((LinearMap.snd A (Fin n → Rf) (Fin n → B)).comp
        (LinearMap.snd A (Fin n → Rf) ((Fin n → Rf) × (Fin n → B)))))

/-- The auxiliary fibre product `P`. -/
private noncomputable def blPbModule (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    Submodule A ((Fin n → Rf) × (Fin n → Rf) × (Fin n → B)) :=
  LinearMap.ker (blPbDelta A B Rf Bf ρ n g)

private lemma bl_mem_pbModule (v : (Fin n → Rf) × (Fin n → Rf) × (Fin n → B)) :
    v ∈ blPbModule A B Rf Bf ρ n g ↔
      ∀ i, g (fun j => ρ (v.1 j)) i = ρ (v.2.1 i) + algebraMap B Bf (v.2.2 i) := by
  simp [blPbModule, blPbDelta, blIotaPi, LinearMap.mem_ker, funext_iff, sub_sub, sub_eq_zero,
    LinearMap.compLeft, Function.comp_def]

/-- First projection `P → (Fin n → Rf)`. -/
private noncomputable def blPbFst (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    ↥(blPbModule A B Rf Bf ρ n g) →ₗ[A] (Fin n → Rf) :=
  (LinearMap.fst A (Fin n → Rf) ((Fin n → Rf) × (Fin n → B))).comp
    (blPbModule A B Rf Bf ρ n g).subtype

/-- Second projection `P → (Fin n → Rf)`. -/
private noncomputable def blPbSnd (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    ↥(blPbModule A B Rf Bf ρ n g) →ₗ[A] (Fin n → Rf) :=
  ((LinearMap.fst A (Fin n → Rf) (Fin n → B)).comp
      (LinearMap.snd A (Fin n → Rf) ((Fin n → Rf) × (Fin n → B)))).comp
    (blPbModule A B Rf Bf ρ n g).subtype

private lemma bl_inclN_mem (t : ↥(gluedModule A B Rf Bf ρ n g)) :
    (((t : (Fin n → Rf) × (Fin n → B)).1, (0 : Fin n → Rf),
      (t : (Fin n → Rf) × (Fin n → B)).2)) ∈ blPbModule A B Rf Bf ρ n g := by
  rw [bl_mem_pbModule]
  intro i
  simpa using (bl_mem_gluedModule _).1 t.2 i

/-- The inclusion `N → P`. -/
private noncomputable def blInclN (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    ↥(gluedModule A B Rf Bf ρ n g) →ₗ[A] ↥(blPbModule A B Rf Bf ρ n g) :=
  LinearMap.codRestrict (blPbModule A B Rf Bf ρ n g)
    (((LinearMap.fst A (Fin n → Rf) (Fin n → B)).prod
        ((0 : ((Fin n → Rf) × (Fin n → B)) →ₗ[A] (Fin n → Rf)).prod
          (LinearMap.snd A (Fin n → Rf) (Fin n → B)))).comp
      (gluedModule A B Rf Bf ρ n g).subtype)
    bl_inclN_mem

/-- The canonical map `(Fin n → A) → (Fin n → Rf)`. -/
private noncomputable def blInclRf (A : Type u) [CommRing A]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf] (n : ℕ) :
    (Fin n → A) →ₗ[A] (Fin n → Rf) :=
  (Algebra.linearMap A Rf).compLeft (Fin n)

private lemma bl_omega_mem (a : Fin n → A) :
    (((0 : Fin n → Rf), (fun i => algebraMap A Rf (a i)),
      (fun i => -(algebraMap A B (a i))))) ∈ blPbModule A B Rf Bf ρ n g := by
  rw [bl_mem_pbModule]
  intro i
  have h0 : (fun j => ρ (((0 : Fin n → Rf),
      (fun i => algebraMap A Rf (a i)), (fun i => -(algebraMap A B (a i)))).1 j)) =
      (0 : Fin n → Bf) := by
    funext j
    simp
  rw [h0, map_zero]
  show (0 : Bf) = ρ (algebraMap A Rf (a i)) + algebraMap B Bf (-(algebraMap A B (a i)))
  rw [ρ.commutes, bl_algebraMap_eq (A := A) (B := B) (Bf := Bf) (a i), map_neg]
  ring

/-- The map `(Fin n → A) → P` whose image is the kernel of the first projection. -/
private noncomputable def blOmega (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    (Fin n → A) →ₗ[A] ↥(blPbModule A B Rf Bf ρ n g) :=
  LinearMap.codRestrict (blPbModule A B Rf Bf ρ n g)
    ((0 : (Fin n → A) →ₗ[A] (Fin n → Rf)).prod
      ((blInclRf A Rf n).prod (-((Algebra.linearMap A B).compLeft (Fin n)))))
    bl_omega_mem

private lemma bl_pbFst_surjective (hB : IsCompletionLike A f B) :
    Function.Surjective ⇑(blPbFst A B Rf Bf ρ n g) := by
  intro x
  obtain ⟨y, b, hyb⟩ := bl_density hB ρ (fun i => g (fun j => ρ (x j)) i)
  exact ⟨⟨(x, y, b), (bl_mem_pbModule _).2 hyb⟩, rfl⟩

private lemma bl_pbSnd_surjective (hB : IsCompletionLike A f B) :
    Function.Surjective ⇑(blPbSnd A B Rf Bf ρ n g) := by
  intro y
  obtain ⟨x, b, hxb⟩ := bl_q_surj' (ρ := ρ) hB (fun i => ρ (y i))
  exact ⟨⟨(x, y, b), (bl_mem_pbModule _).2 hxb⟩, rfl⟩

private lemma bl_inclN_injective :
    Function.Injective ⇑(blInclN A B Rf Bf ρ n g) := by
  intro t s h
  apply Subtype.ext
  have h1 : ((blInclN A B Rf Bf ρ n g t : ↥(blPbModule A B Rf Bf ρ n g)) :
      (Fin n → Rf) × (Fin n → Rf) × (Fin n → B)) = (blInclN A B Rf Bf ρ n g s : _) :=
    congrArg _ h
  exact Prod.ext (congrArg (·.1) h1) (congrArg (·.2.2) h1)

private lemma bl_exact_inclN_pbSnd :
    Function.Exact ⇑(blInclN A B Rf Bf ρ n g) ⇑(blPbSnd A B Rf Bf ρ n g) := by
  rintro ⟨⟨x, y, b⟩, hmem⟩
  constructor
  · intro hz
    have hy : y = 0 := hz
    subst hy
    rw [bl_mem_pbModule] at hmem
    have hg : ((x, b) : (Fin n → Rf) × (Fin n → B)) ∈ gluedModule A B Rf Bf ρ n g := by
      rw [bl_mem_gluedModule]
      intro i
      simpa using hmem i
    exact ⟨⟨(x, b), hg⟩, rfl⟩
  · rintro ⟨t, ht⟩
    rw [← ht]
    rfl

private lemma bl_exact_omega_pbFst (hB : IsCompletionLike A f B) (hBf : IsSMulRegular B f) :
    Function.Exact ⇑(blOmega A B Rf Bf ρ n g) ⇑(blPbFst A B Rf Bf ρ n g) := by
  rintro ⟨⟨x, y, b⟩, hmem⟩
  constructor
  · intro hz
    have hx : x = 0 := hz
    subst hx
    rw [bl_mem_pbModule] at hmem
    have h0 : ∀ i, ρ (y i) = algebraMap B Bf (-(b i)) := by
      intro i
      have hi := hmem i
      have hz0 : (fun j => ρ (((0 : Fin n → Rf), y, b).1 j)) = (0 : Fin n → Bf) := by
        funext j
        simp
      rw [hz0, map_zero] at hi
      have hi' : ρ (y i) + algebraMap B Bf (b i) = 0 := by
        simpa using hi.symm
      rw [map_neg]
      exact eq_neg_of_add_eq_zero_left hi'
    choose a ha1 ha2 using fun i => scalar_pullback_exists hB hBf ρ (y i) (-(b i)) (h0 i)
    refine ⟨a, ?_⟩
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · funext i
      exact ha1 i
    · funext i
      show -(algebraMap A B (a i)) = b i
      rw [ha2 i, neg_neg]
  · rintro ⟨a, ha⟩
    rw [← ha]
    rfl

private lemma bl_pbFst_comp_inclN :
    (blPbFst A B Rf Bf ρ n g).comp (blInclN A B Rf Bf ρ n g) = gluedFst A B Rf Bf ρ n g := rfl

private lemma bl_pbSnd_comp_inclN :
    (blPbSnd A B Rf Bf ρ n g).comp (blInclN A B Rf Bf ρ n g) = 0 := rfl

private lemma bl_pbSnd_comp_omega :
    (blPbSnd A B Rf Bf ρ n g).comp (blOmega A B Rf Bf ρ n g) = blInclRf A Rf n := rfl

/-! #### The comparison map `B ⊗[A] (Fin n → Rf) → (Fin n → Bf)` -/

/-- Multiplication `B ⊗[A] Rf → Bf`. -/
private noncomputable def blPsi1 (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) : B ⊗[A] Rf →ₗ[A] Bf :=
  (LinearMap.mul' A Bf).comp
    (TensorProduct.map (IsScalarTower.toAlgHom A B Bf).toLinearMap ρ.toLinearMap)

private lemma blPsi1_tmul (b : B) (r : Rf) :
    blPsi1 A B Rf Bf ρ (b ⊗ₜ[A] r) = algebraMap B Bf b * ρ r := rfl

/-- Every element of `B ⊗[A] Rf` is a simple tensor `b ⊗ (1 / f ^ k)`. -/
private lemma bl_tensor_normal_form (z : B ⊗[A] Rf) :
    ∃ (b : B) (k : ℕ),
      z = b ⊗ₜ[A] IsLocalization.mk' Rf 1 (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f) := by
  have hstep : ∀ k k' : ℕ,
      IsLocalization.mk' Rf 1 (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f) =
        (f ^ k' : A) •
          IsLocalization.mk' Rf 1 (⟨f ^ (k + k'), ⟨k + k', rfl⟩⟩ : Submonoid.powers f) := by
    intro k k'
    rw [Algebra.smul_def, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq]
    simp [pow_add]
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by rw [TensorProduct.zero_tmul]⟩
  | tmul b r =>
      obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) r
      obtain ⟨k, hk⟩ := m.2
      have hm : m = (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f) := Subtype.ext hk.symm
      subst hm
      refine ⟨a • b, k, ?_⟩
      show b ⊗ₜ[A] IsLocalization.mk' Rf a (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f) =
        (a • b) ⊗ₜ[A] IsLocalization.mk' Rf 1 (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f)
      rw [IsLocalization.mk'_eq_mul_mk'_one, ← Algebra.smul_def]
      exact (TensorProduct.smul_tmul a b _).symm
  | add x y hx hy =>
      obtain ⟨b, k, rfl⟩ := hx
      obtain ⟨b', k', rfl⟩ := hy
      refine ⟨(f ^ k' : A) • b + (f ^ k : A) • b', k + k', ?_⟩
      rw [hstep k k', hstep k' k, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul,
        add_comm k' k, ← TensorProduct.add_tmul]

private lemma bl_Psi1_injective (hBf : IsSMulRegular B f) :
    Function.Injective ⇑(blPsi1 A B Rf Bf ρ) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨b, k, rfl⟩ := bl_tensor_normal_form (Rf := Rf) (f := f) z
  rw [blPsi1_tmul] at hz
  have h1 : algebraMap B Bf b *
      ((algebraMap A Bf f) ^ k *
        ρ (IsLocalization.mk' Rf 1 (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f))) = 0 := by
    rw [show algebraMap B Bf b *
        ((algebraMap A Bf f) ^ k *
          ρ (IsLocalization.mk' Rf 1 (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f))) =
        (algebraMap A Bf f) ^ k *
          (algebraMap B Bf b *
            ρ (IsLocalization.mk' Rf 1 (⟨f ^ k, ⟨k, rfl⟩⟩ : Submonoid.powers f))) from by ring,
      hz, mul_zero]
  rw [bl_rho_mk' ρ 1 k, map_one, mul_one] at h1
  have hb : b = 0 := bl_iota_injective hBf (h1.trans (map_zero (algebraMap B Bf)).symm)
  simp [hb]

/-- The comparison map `B ⊗[A] (Fin n → Rf) → (Fin n → Bf)`. -/
private noncomputable def blPsi (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) : B ⊗[A] (Fin n → Rf) →ₗ[A] (Fin n → Bf) :=
  ((blPsi1 A B Rf Bf ρ).compLeft (Fin n)).comp
    (TensorProduct.piRight A A B (fun _ : Fin n => Rf)).toLinearMap

private lemma blPsi_tmul (b : B) (x : Fin n → Rf) (i : Fin n) :
    blPsi A B Rf Bf ρ n (b ⊗ₜ[A] x) i = algebraMap B Bf b * ρ (x i) := rfl

private lemma bl_Psi_injective (hBf : IsSMulRegular B f) :
    Function.Injective ⇑(blPsi A B Rf Bf ρ n) := by
  intro v w h
  refine (TensorProduct.piRight A A B (fun _ : Fin n => Rf)).injective (funext fun i => ?_)
  exact bl_Psi1_injective hBf (congrFun h i)

omit [IsLocalization.Away f Rf] in
private lemma bl_Psi_comp_inclRf_injective (hBf : IsSMulRegular B f) :
    Function.Injective ⇑((blPsi A B Rf Bf ρ n).comp
      (LinearMap.lTensor B (blInclRf A Rf n))) := by
  have key : (blPsi A B Rf Bf ρ n).comp (LinearMap.lTensor B (blInclRf A Rf n)) =
      (blIotaPi A B Bf n).comp (TensorProduct.piScalarRight A A B (Fin n)).toLinearMap := by
    refine TensorProduct.ext' fun b a => ?_
    funext i
    simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, blPsi_tmul, blIotaPi_apply,
      blInclRf, LinearMap.compLeft_apply, LinearEquiv.coe_coe,
      TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul, Algebra.smul_def]
    have hc : ρ ((⇑(Algebra.linearMap A Rf) ∘ a) i) = algebraMap A Bf (a i) := by
      simp [ρ.commutes]
    rw [hc, bl_algebraMap_eq (A := A) (B := B) (a i), ← map_mul]
    ring_nf
  rw [key]
  intro v w hvw
  simp only [LinearMap.comp_apply] at hvw
  refine (TensorProduct.piScalarRight A A B (Fin n)).injective (funext fun i => ?_)
  exact bl_iota_injective hBf (congrFun hvw i)

/-- `(Fin n → Rf)` is `A`-flat, being a finite product of localisations. -/
private lemma bl_flat (A : Type u) [CommRing A] (f : A)
    (Rf : Type u) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf] (n : ℕ) :
    Module.Flat A (Fin n → Rf) := by
  have : Module.Flat A Rf := IsLocalization.flat Rf (Submonoid.powers f)
  exact Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype A (Fin n) fun _ => Rf).symm

/-! #### The base change map -/

/-- The base change map `B ⊗[A] N → (Fin n → B)`. -/
private noncomputable def blPhi (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    B ⊗[A] ↥(gluedModule A B Rf Bf ρ n g) →ₗ[B] (Fin n → B) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.smulRight (LinearMap.id : B →ₗ[B] B) (gluedSnd A B Rf Bf ρ n g))

private lemma blPhi_tmul (b : B) (t : ↥(gluedModule A B Rf Bf ρ n g)) :
    blPhi A B Rf Bf ρ n g (b ⊗ₜ[A] t) = b • gluedSnd A B Rf Bf ρ n g t := rfl

/-- The commuting square relating `blPhi` and `blPsi`. -/
private lemma bl_key_square :
    (blIotaPi A B Bf n).comp ((blPhi A B Rf Bf ρ n g).restrictScalars A) =
      (g.toLinearMap.restrictScalars A).comp
        ((blPsi A B Rf Bf ρ n).comp
          (LinearMap.lTensor B (gluedFst A B Rf Bf ρ n g))) := by
  refine TensorProduct.ext' fun b t => ?_
  have ht : ∀ i, g (fun j => ρ ((t : (Fin n → Rf) × (Fin n → B)).1 j)) i =
      algebraMap B Bf ((t : (Fin n → Rf) × (Fin n → B)).2 i) :=
    (bl_mem_gluedModule _).1 t.2
  have hsm : (fun i => algebraMap B Bf b * ρ ((t : (Fin n → Rf) × (Fin n → B)).1 i)) =
      algebraMap B Bf b • (fun i => ρ ((t : (Fin n → Rf) × (Fin n → B)).1 i)) := rfl
  funext i
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, blPhi_tmul,
    LinearMap.lTensor_tmul, bl_gluedFst_apply, blIotaPi_apply, bl_gluedSnd_apply,
    LinearEquiv.coe_coe]
  have hb : blPsi A B Rf Bf ρ n (b ⊗ₜ[A] (t : (Fin n → Rf) × (Fin n → B)).1) =
      algebraMap B Bf b • (fun i => ρ ((t : (Fin n → Rf) × (Fin n → B)).1 i)) := by
    funext j
    rw [blPsi_tmul]
    rfl
  rw [hb, map_smul]
  simp [ht i, Pi.smul_apply, smul_eq_mul, map_mul]

private lemma bl_Phi_surjective (hB : IsCompletionLike A f B) :
    Function.Surjective ⇑(blPhi A B Rf Bf ρ n g) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← bl_span_eq_top (ρ := ρ) (g := g) hB,
    Submodule.span_le]
  rintro _ ⟨t, rfl⟩
  exact ⟨(1 : B) ⊗ₜ[A] t, by simp [blPhi_tmul]⟩

private lemma bl_Phi_injective (hB : IsCompletionLike A f B) (hBf : IsSMulRegular B f) :
    Function.Injective ⇑(blPhi A B Rf Bf ρ n g) := by
  haveI : Module.Flat A (Fin n → Rf) := bl_flat A f Rf n
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hsq := congrArg (fun φ => φ t) (bl_key_square (ρ := ρ) (g := g))
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, ht, map_zero,
    LinearEquiv.coe_coe] at hsq
  have h1 : blPsi A B Rf Bf ρ n (LinearMap.lTensor B (gluedFst A B Rf Bf ρ n g) t) = 0 := by
    have := hsq.symm
    simpa using (LinearEquiv.map_eq_zero_iff g).1 (by simpa using this)
  have h2 : LinearMap.lTensor B (gluedFst A B Rf Bf ρ n g) t = 0 :=
    (LinearMap.map_eq_zero_iff _ (bl_Psi_injective hBf)).1 h1
  set tt := LinearMap.lTensor B (blInclN A B Rf Bf ρ n g) t with htt
  have h3 : LinearMap.lTensor B (blPbFst A B Rf Bf ρ n g) tt = 0 := by
    rw [htt, ← LinearMap.lTensor_comp_apply, bl_pbFst_comp_inclN]
    exact h2
  obtain ⟨u, hu⟩ :=
    (lTensor_exact B (bl_exact_omega_pbFst hB hBf) (bl_pbFst_surjective hB) tt).1 h3
  have h4 : LinearMap.lTensor B (blPbSnd A B Rf Bf ρ n g) tt = 0 := by
    rw [htt, ← LinearMap.lTensor_comp_apply, bl_pbSnd_comp_inclN]
    simp
  have h5 : LinearMap.lTensor B (blInclRf A Rf n) u = 0 := by
    rw [← bl_pbSnd_comp_omega (B := B) (Bf := Bf) (ρ := ρ) (g := g), LinearMap.lTensor_comp_apply, hu]
    exact h4
  have h6 : u = 0 := by
    refine (LinearMap.map_eq_zero_iff _ (bl_Psi_comp_inclRf_injective (ρ := ρ) (n := n) hBf)).1 ?_
    simp [h5]
  have h7 : tt = 0 := by rw [← hu, h6, map_zero]
  exact (LinearMap.map_eq_zero_iff _
    (LinearMap.lTensor_injective_of_exact_of_flat (blPbSnd A B Rf Bf ρ n g)
      (bl_pbSnd_surjective hB) (blInclN A B Rf Bf ρ n g) bl_inclN_injective
      bl_exact_inclN_pbSnd B)).1 h7

end Aux

/-- The second projection exhibits `(Fin n → B)` as the base change of the glued
module along `A → B`. -/
theorem gluedSnd_isBaseChange
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (hA : IsSMulRegular A f) (hBf : IsSMulRegular B f)
    (Rf : Type u) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    [IsLocalization.Away (algebraMap A B f) Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    IsBaseChange B (gluedSnd A B Rf Bf ρ n g) := by
  refine IsBaseChange.of_equiv
    (LinearEquiv.ofBijective (blPhi A B Rf Bf ρ n g)
      ⟨bl_Phi_injective hB hBf, bl_Phi_surjective hB⟩) ?_
  intro t
  simp [blPhi_tmul]
/- ===== node D12 (D12_a3): verified by Aristotle ===== -/
/-! ### Auxiliary material for `gluedModule_finite_projective`

The proof is elementary.  Write `ι : B → Bf` for the canonical map and
`ψ : (Fin n → A) → (Fin n → Rf)` for the componentwise structure map.  Choosing a common
denominator `f ^ K` for `g` and `g⁻¹` produces matrices `V`, `W` over `B` with
`f ^ K • g (ι ∘ b) = ι ∘ (V *ᵥ b)` and `f ^ K • g⁻¹ (ι ∘ b) = ι ∘ (W *ᵥ b)`, whence
`W * V = f ^ κ` with `κ = 2 * K`.  The glued module `M` embeds into `Fin n → A` via
`(x, y) ↦ a` where `ψ a = f ^ K • x` (this uses the arithmetic square `A = Rf ×_{Bf} B`),
with image `L = {a | a_B ∈ W *ᵥ B ^ n}`.  Approximating `W`, `V` by matrices `Wh`, `Vh`
over `A` modulo `f ^ m`, `m = 2 * κ` (possible since `A / f ^ m ≅ B / f ^ m`), one gets
`Wh * Vh = f ^ κ + f ^ m • S`, `Vh * Wh = f ^ κ + f ^ m • S'` and `L = Wh *ᵥ A ^ n + f ^ κ • A ^ n`.
Then `a ↦ (f ^ (-κ) • (Vh *ᵥ a), -(S *ᵥ a))` is a section of `(b, c) ↦ Wh *ᵥ b + f ^ κ • c`,
so `L`, and hence `M`, is a direct summand of `A ^ (2 * n)`, thus finite projective.
-/

section Aux

variable {A : Type u} [CommRing A] {f : A}
  {B : Type u} [CommRing B] [Algebra A B]
  {Rf : Type u} [CommRing Rf] [Algebra A Rf]
  {Bf : Type u} [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]

/-- A linear map whose range is contained in the range of an injective linear map factors
through it. -/
private lemma exists_factor {M N P : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (i : N →ₗ[A] P) (hi : Function.Injective i) (t : M →ₗ[A] P)
    (h : ∀ x, ∃ y, i y = t x) : ∃ s : M →ₗ[A] N, ∀ x, i (s x) = t x := by
  choose s hs using h
  refine ⟨{ toAddHom := { toFun := s, map_add' := ?_ }, map_smul' := ?_ }, hs⟩
  · intro x y
    exact hi (by simp [hs, t.map_add])
  · intro a x
    exact hi (by simp [hs, t.map_smul])

/-- A module which is a direct summand of a finite projective module is finite projective. -/
private lemma finite_projective_of_split {M P : Type u} [AddCommGroup M] [Module A M]
    [AddCommGroup P] [Module A P] [Module.Finite A P] [Module.Projective A P]
    (j : M →ₗ[A] P) (r : P →ₗ[A] M) (h : ∀ x, r (j x) = x) :
    Module.Finite A M ∧ Module.Projective A M := by
  refine ⟨Module.Finite.of_surjective r fun x => ⟨j x, h x⟩, Module.Projective.of_split j r ?_⟩
  exact LinearMap.ext h

private lemma injective_algebraMap_Rf [IsLocalization.Away f Rf] (hA : IsSMulRegular A f) :
    Function.Injective (algebraMap A Rf) := by
  intro x y hxy
  have hpow : Submonoid.powers f ≤ nonZeroDivisors A := by
    intro s hs
    simp only [Submonoid.mem_powers_iff] at hs
    obtain ⟨n, rfl⟩ := hs
    have h := IsSMulRegular.pow n hA
    constructor <;> intro a ha
    · exact h (by simp [ha])
    · exact h (by simp [mul_comm, ha])
  exact IsLocalization.injective (R := A) (S := Rf) (M := Submonoid.powers f) hpow hxy

private lemma injective_algebraMap_Bf [IsLocalization.Away (algebraMap A B f) Bf]
    (hBf : IsSMulRegular B f) : Function.Injective (algebraMap B Bf) := by
  haveI : IsLocalization (Submonoid.powers (algebraMap A B f)) Bf := by assumption_mod_cast
  intro b₁ b₂ heq
  rw [IsLocalization.eq_iff_exists (R := B) (S := Bf)
    (M := Submonoid.powers (algebraMap A B f))] at heq
  obtain ⟨c, hc⟩ := heq
  have hc_mem : c.val ∈ Submonoid.powers (algebraMap A B f) := c.property
  rw [Submonoid.mem_powers_iff] at hc_mem
  obtain ⟨n, hn⟩ := hc_mem
  have hreg : IsSMulRegular B ((algebraMap A B f) ^ n) := by
    intro x y hxy
    have hreg' := hBf.pow n
    show x = y
    have heq : ((algebraMap A B) f) ^ n = (algebraMap A B) (f ^ n) := (map_pow _ _ _).symm
    rw [heq] at hxy
    exact hreg' (by simpa [Algebra.smul_def] using hxy)
  rw [← hn] at hc
  exact hreg hc

/-- Multiplication by `f ^ K` is injective on `Rf ^ n`. -/
private lemma smul_pow_injective_Rf [IsLocalization.Away f Rf] {n K : ℕ} {v w : Fin n → Rf}
    (h : (f ^ K : A) • v = (f ^ K : A) • w) : v = w := by
  have hf_unit : IsUnit (algebraMap A Rf f) :=
    IsLocalization.map_units _ (⟨f, 1, pow_one f⟩ : Submonoid.powers f)
  have hunit : IsUnit (algebraMap A Rf (f ^ K)) := by rw [map_pow]; exact hf_unit.pow K
  ext i
  have hi := congr_fun h i
  simp only [Pi.smul_apply, Algebra.smul_def] at hi
  obtain ⟨u, hu⟩ := hunit
  rw [← hu, mul_comm (↑u) (v i), mul_comm (↑u) (w i)] at hi
  exact u.mul_left_inj.mp hi

/-- Multiplication by `f ^ K` is injective on `Bf ^ n`. -/
private lemma smul_pow_injective_Bf [IsLocalization.Away (algebraMap A B f) Bf] {n K : ℕ}
    {v w : Fin n → Bf} (h : (f ^ K : A) • v = (f ^ K : A) • w) : v = w := by
  have hf_unit : IsUnit (algebraMap B Bf (algebraMap A B f)) :=
    IsLocalization.map_units _
      (⟨algebraMap A B f, 1, by simp⟩ : Submonoid.powers (algebraMap A B f))
  have hfK_unit : IsUnit (algebraMap B Bf ((algebraMap A B f) ^ K)) := by
    rw [map_pow]; exact hf_unit.pow K
  have heq : algebraMap B Bf ((algebraMap A B f) ^ K) = algebraMap A Bf (f ^ K) := by
    rw [← map_pow]
    simp [IsScalarTower.algebraMap_apply A B Bf]
  rw [heq] at hfK_unit
  ext i
  have hi := congr_fun h i
  simp only [Pi.smul_apply, Algebra.smul_def] at hi
  obtain ⟨u, hu⟩ := hfK_unit
  rw [← hu, mul_comm (↑u) (v i), mul_comm (↑u) (w i)] at hi
  exact u.mul_left_inj.mp hi

/-- Every element of `B` is congruent to an element of `A` modulo `f ^ m`. -/
private lemma exists_approx (hB : IsCompletionLike A f B) {m : ℕ} (hm : 0 < m) (b : B) :
    ∃ (a : A) (c : B), b = algebraMap A B a + (f ^ m : A) • c := by
  -- Use surjectivity of A → B/(f^m)B
  have hsurj := hB.surjective_mod m hm
  -- Get a : A mapping to the same element as b in the quotient
  obtain ⟨a, ha⟩ := hsurj (Ideal.Quotient.mk _ b)
  -- algebraMap A (B ⧸ I) = Ideal.Quotient.mk I ∘ algebraMap A B
  have : algebraMap A (B ⧸ Ideal.map (algebraMap A B) (Ideal.span {f ^ m})) =
      (Ideal.Quotient.mk _).comp (algebraMap A B) := by
    ext x
    rfl
  rw [this] at ha
  simp only [RingHom.comp_apply] at ha
  rw [Ideal.Quotient.eq] at ha
  -- The ideal is spanned by algebraMap A B (f^m) = (algebraMap A B f)^m
  have helm : Ideal.map (algebraMap A B) (Ideal.span {f ^ m}) = Ideal.span {(algebraMap A B f) ^ m} := by
    rw [Ideal.map_span]
    simp [Set.image_singleton, map_pow]
  rw [helm] at ha
  -- Elements of Ideal.span {g} are of the form g * c
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
  -- hc : algebraMap A B a - b = (algebraMap A B f)^m * c
  use a, -c
  have heq : (f ^ m : A) • (-c) = (algebraMap A B f) ^ m * (-c) := by
    rw [Algebra.smul_def, map_pow]
  rw [heq]
  linear_combination -hc

/-- An element of `A` divisible by `f ^ m` in `B` is divisible by `f ^ m` in `A`. -/
private lemma exists_div (hB : IsCompletionLike A f B) {m : ℕ} (hm : 0 < m) (a : A) (c : B)
    (h : algebraMap A B a = (f ^ m : A) • c) : ∃ a' : A, a = f ^ m * a' := by
  have h1 : (algebraMap A B) a ∈ (Ideal.span {f ^ m}).map (algebraMap A B) := by
    rw [h, Algebra.smul_def]
    exact Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem (algebraMap A B) (Ideal.mem_span_singleton_self (f ^ m : A)))
  refine Ideal.mem_span_singleton.mp ?_
  exact hB.ker_mod m hm ▸ Ideal.Quotient.eq_zero_iff_mem.mpr h1

private lemma exists_approx_vec (hB : IsCompletionLike A f B) {m : ℕ} (hm : 0 < m) {n : ℕ}
    (y : Fin n → B) : ∃ (α : Fin n → A) (y' : Fin n → B),
      y = (fun i => algebraMap A B (α i)) + (f ^ m : A) • y' := by
  choose a c hac using fun i => exists_approx hB hm (y i)
  exact ⟨a, c, funext fun i => hac i⟩

private lemma exists_div_vec (hB : IsCompletionLike A f B) {m : ℕ} (hm : 0 < m) {n : ℕ}
    (a : Fin n → A) (c : Fin n → B)
    (h : (fun i => algebraMap A B (a i)) = (f ^ m : A) • c) :
    ∃ a' : Fin n → A, a = (f ^ m : A) • a' := by
  have h2 : ∀ i, algebraMap A B (a i) = (f ^ m : A) • c i := by
    intro i
    have := congr_fun h i
    simp [Pi.smul_def] at this
    exact this
  choose a' ha' using fun i => exists_div hB hm (a i) (c i) (h2 i)
  exact ⟨a', funext ha'⟩

private lemma exists_lift_matrix (hB : IsCompletionLike A f B) {m : ℕ} (hm : 0 < m) {n : ℕ}
    (W : Matrix (Fin n) (Fin n) B) :
    ∃ (Wh : Matrix (Fin n) (Fin n) A) (T : Matrix (Fin n) (Fin n) B),
      Wh.map (algebraMap A B) = W + (f ^ m : A) • T := by
  choose a c hac using fun i j => exists_approx hB hm (W i j)
  use Matrix.of a, Matrix.of (fun i j => -c i j)
  ext i j
  simp [hac i j]

private lemma exists_div_matrix (hB : IsCompletionLike A f B) {m : ℕ} (hm : 0 < m) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) A) (Y : Matrix (Fin n) (Fin n) B)
    (h : X.map (algebraMap A B) = (f ^ m : A) • Y) :
    ∃ Z : Matrix (Fin n) (Fin n) A, X = (f ^ m : A) • Z := by
  have := fun i => exists_div_vec hB hm (fun j => X i j) (fun j => Y i j) ?_
  · choose Z hZ using this
    exact ⟨Z, by ext i j; simp [hZ]⟩
  · ext j
    simp [Pi.smul_def]
    exact congr_fun (congr_fun h i) j

/-- The arithmetic square: an element of `Rf` whose image in `Bf` comes from `B` comes
from `A`. -/
private lemma exists_preimage_of_glue [IsLocalization.Away f Rf]
    [IsLocalization.Away (algebraMap A B f) Bf] (hB : IsCompletionLike A f B)
    (hA : IsSMulRegular A f) (hBf : IsSMulRegular B f) (ρ : Rf →ₐ[A] Bf)
    (r : Rf) (b : B) (h : ρ r = algebraMap B Bf b) :
    ∃ a : A, algebraMap A Rf a = r := by
  obtain ⟨⟨s, t, ht⟩, hrs⟩ :=
    IsLocalization.mk'_surjective (M := Submonoid.powers f) (R := A) (S := Rf) r
  simp only [Submonoid.mem_powers_iff] at ht
  obtain ⟨m, rfl⟩ := ht
  have hmul : (algebraMap A Rf (f ^ m)) * r = algebraMap A Rf s := by
    rw [← hrs]
    simp only [RingHom.map_pow]
    rw [mul_comm, ← RingHom.map_pow, IsLocalization.mk'_spec (S := Rf)]
  have hmul' : (algebraMap A Bf (f ^ m)) * ρ r = algebraMap A Bf s := by
    have hc := congr_arg ρ hmul
    simp only [map_mul, AlgHom.map_algebraMap, map_pow] at hc
    rw [← map_pow] at hc
    exact hc
  rw [h] at hmul'
  have hscalar : ∀ x : A, algebraMap A Bf x = algebraMap B Bf (algebraMap A B x) := fun x =>
    IsScalarTower.algebraMap_apply A B Bf x
  rw [hscalar, hscalar, RingHom.map_pow] at hmul'
  have hinj : Function.Injective (algebraMap B Bf) := injective_algebraMap_Bf hBf
  rw [← map_mul] at hmul'
  have hmul'' : (algebraMap A B) f ^ m * b = (algebraMap A B) s := hinj hmul'
  rw [← RingHom.map_pow, ← Algebra.smul_def, eq_comm] at hmul''
  by_cases hm : 0 < m
  · obtain ⟨a', ha'⟩ := exists_div hB hm s b hmul''
    refine ⟨a', ?_⟩
    rw [ha', RingHom.map_mul] at hmul
    have hunit : IsUnit (algebraMap A Rf (f ^ m)) :=
      IsLocalization.map_units Rf (⟨f ^ m, m, rfl⟩ : Submonoid.powers f)
    exact hunit.mul_left_cancel hmul.symm
  · have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst hm0
    refine ⟨s, ?_⟩
    simp only [pow_zero] at hrs ⊢
    rw [← hrs]
    exact (IsLocalization.mk'_one Rf s).symm

/-- A finite family of elements of `Bf` becomes integral after multiplication by a large
enough power of `f`. -/
private lemma exists_common_denominator [IsLocalization.Away (algebraMap A B f) Bf] {n : ℕ}
    (v : Fin n → Fin n → Bf) :
    ∃ K : ℕ, ∀ K' : ℕ, K ≤ K' → ∃ V : Matrix (Fin n) (Fin n) B,
      ∀ i j, (f ^ K' : A) • v i j = algebraMap B Bf (V i j) := by
  have h_each : ∀ i j, ∃ k : ℕ, ∃ b : B, (f ^ k : A) • v i j = algebraMap B Bf b := by
    intro i j
    rcases IsLocalization.mk'_surjective (Submonoid.powers (algebraMap A B f)) (v i j) with
      ⟨⟨b, k⟩, hk⟩
    obtain ⟨m, hm⟩ := k.prop
    refine ⟨m, b, ?_⟩
    rw [← hk, Algebra.smul_def]
    simp only [map_pow]
    rw [IsScalarTower.algebraMap_apply A B Bf, ← map_pow,
      show (algebraMap A B) f ^ m = k from hm]
    simp [IsLocalization.mk'_mul_cancel_right (R := B) (S := Bf) b]
  choose k b hkb using h_each
  refine ⟨Finset.univ.sup fun i => Finset.univ.sup fun j => k i j, fun K' hK' => ?_⟩
  refine ⟨fun i j => (algebraMap A B (f ^ (K' - k i j))) * b i j, fun i j => ?_⟩
  have hk' : k i j ≤ K' := by
    calc k i j ≤ Finset.univ.sup fun j => k i j := Finset.le_sup (Finset.mem_univ j)
      _ ≤ Finset.univ.sup fun i => Finset.univ.sup fun j => k i j :=
          Finset.le_sup_of_le (Finset.mem_univ i) (le_refl _)
      _ ≤ K' := hK'
  calc (f ^ K' : A) • v i j
      = (f ^ (K' - k i j) * f ^ (k i j) : A) • v i j := by rw [← pow_add, Nat.sub_add_cancel hk']
    _ = (f ^ (K' - k i j) : A) • (f ^ (k i j) • v i j) := by rw [mul_smul]
    _ = (f ^ (K' - k i j) : A) • algebraMap B Bf (b i j) := by rw [hkb]
    _ = algebraMap B Bf ((algebraMap A B (f ^ (K' - k i j))) * b i j) := by
        rw [Algebra.smul_def, map_mul]
        congr 1
        exact IsScalarTower.algebraMap_apply A B Bf _

/-- A `Bf`-linear endomorphism given on the standard basis by a matrix over `B` (up to the
denominator `f ^ K`) is given by that matrix on all integral vectors. -/
private lemma denominator_matrix_apply [IsLocalization.Away (algebraMap A B f) Bf] {n K : ℕ}
    (F : (Fin n → Bf) →ₗ[Bf] (Fin n → Bf)) (V : Matrix (Fin n) (Fin n) B)
    (hV : ∀ i j, (f ^ K : A) • F (fun i' => algebraMap B Bf ((Pi.single j 1 : Fin n → B) i')) i
      = algebraMap B Bf (V i j)) :
    ∀ b : Fin n → B, (f ^ K : A) • F (fun i => algebraMap B Bf (b i))
      = fun i => algebraMap B Bf (V.mulVec b i) := by
  intro b
  have hb : (fun i => algebraMap B Bf (b i)) =
      ∑ j : Fin n, (algebraMap B Bf (b j)) • (fun i => if i = j then (1 : Bf) else 0) := by
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    conv_rhs => rw [Finset.sum_congr rfl fun j _ => by rw [mul_ite, mul_one, mul_zero]]
    rw [Finset.sum_ite_eq]
    simp
  rw [hb, map_sum, Finset.smul_sum]
  simp_rw [map_smul]
  have heq : ∀ x : Fin n, (fun i => if i = x then (1 : Bf) else 0) =
      (fun i' => (algebraMap B Bf) ((Pi.single x 1 : Fin n → B) i')) := by
    intro x
    ext i'
    simp [Pi.single_apply]
  simp_rw [heq]
  have hassoc : ∀ x, f ^ K • (algebraMap B Bf) (b x) •
        F (fun i' => (algebraMap B Bf) ((Pi.single x 1 : Fin n → B) i')) =
      (algebraMap B Bf) (b x) •
        (f ^ K • F (fun i' => (algebraMap B Bf) ((Pi.single x 1 : Fin n → B) i'))) := by
    intro x
    rw [smul_comm]
  simp_rw [hassoc]
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [hV]
  simp_rw [← RingHom.map_mul]
  rw [← map_sum]
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- A `Bf`-linear endomorphism of `Bf ^ n` is given, after multiplication by a suitable power
of `f`, by a matrix over `B`. -/
private lemma exists_denominator_matrix [IsLocalization.Away (algebraMap A B f) Bf] {n : ℕ}
    (F : (Fin n → Bf) →ₗ[Bf] (Fin n → Bf)) :
    ∃ K : ℕ, ∀ K' : ℕ, K ≤ K' → ∃ V : Matrix (Fin n) (Fin n) B,
      ∀ b : Fin n → B, (f ^ K' : A) • F (fun i => algebraMap B Bf (b i))
        = fun i => algebraMap B Bf (V.mulVec b i) := by
  obtain ⟨K, hK⟩ := exists_common_denominator (A := A) (f := f) (B := B)
    (fun i j => F (fun i' => algebraMap B Bf ((Pi.single j 1 : Fin n → B) i')) i)
  refine ⟨K, fun K' hK' => ?_⟩
  obtain ⟨V, hV⟩ := hK K' hK'
  exact ⟨V, denominator_matrix_apply F V hV⟩

private lemma matrix_mul_eq_pow [IsLocalization.Away (algebraMap A B f) Bf]
    (hBf : IsSMulRegular B f) {n K : ℕ} {g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)}
    {V W : Matrix (Fin n) (Fin n) B}
    (hV : ∀ b : Fin n → B, (f ^ K : A) • g (fun i => algebraMap B Bf (b i))
      = fun i => algebraMap B Bf (V.mulVec b i))
    (hW : ∀ b : Fin n → B, (f ^ K : A) • g.symm (fun i => algebraMap B Bf (b i))
      = fun i => algebraMap B Bf (W.mulVec b i)) :
    W * V = (f ^ (2 * K) : A) • (1 : Matrix (Fin n) (Fin n) B) := by
  have hinj : Function.Injective (algebraMap B Bf) := injective_algebraMap_Bf hBf
  have emb_inj : Function.Injective (fun v : Fin n → B => fun i => algebraMap B Bf (v i)) := by
    intro v w hvw
    ext i
    exact hinj (congr_fun hvw i)
  have key : ∀ b : Fin n → B,
      (f ^ (2 * K) : A) • (fun i => (algebraMap B Bf) (b i) : Fin n → Bf) =
      fun i => (algebraMap B Bf) ((W * V).mulVec b i) := by
    intro b
    have hv := hV b
    set c := V.mulVec b with hc
    have hw := hW c
    have step1 : g.symm (fun i => algebraMap B Bf (c i))
        = (f ^ K : A) • fun i => algebraMap B Bf (b i) := by
      have hv' : (algebraMap A Bf) (f ^ K) • g (fun i => algebraMap B Bf (b i))
          = fun i => algebraMap B Bf (c i) := by
        convert hv using 1
        ext i
        simp [Algebra.smul_def]
      have hstep : g.symm (fun i => algebraMap B Bf (c i))
          = g.symm ((algebraMap A Bf) (f ^ K) • g (fun i => algebraMap B Bf (b i))) := by
        rw [hv']
      rw [hstep, map_smul]
      simp [LinearEquiv.symm_apply_apply, Algebra.smul_def]
      rfl
    have step2 : (f ^ (2 * K) : A) • (fun i => (algebraMap B Bf) (b i) : Fin n → Bf) =
        (f ^ K : A) • ((f ^ K : A) • (fun i => (algebraMap B Bf) (b i) : Fin n → Bf)) := by
      ext i
      simp [Algebra.smul_def]
      ring
    rw [step2, ← step1, hw, Matrix.mulVec_mulVec]
  ext i j
  have emb_eq := key (fun k => if k = j then (1 : B) else 0)
  have emb_eq' : (fun v : Fin n → B => fun i => (algebraMap B Bf) (v i))
        ((f ^ (2 * K) : A) • (fun k => if k = j then (1 : B) else 0)) =
      (fun v : Fin n → B => fun i => (algebraMap B Bf) (v i))
        ((W * V).mulVec (fun k => if k = j then (1 : B) else 0)) := by
    convert emb_eq using 2
    ext i
    simp only [Algebra.smul_def, Pi.smul_apply]
    split_ifs with h
    · rw [map_mul, RingHom.map_pow (algebraMap A B) f (2 * K),
        RingHom.map_pow (algebraMap B Bf) _ _, RingHom.map_pow (algebraMap A Bf) f (2 * K),
        IsScalarTower.algebraMap_apply A B Bf f]
    · simp
  have hemb := emb_inj emb_eq'
  have hi := congr_fun hemb i
  simp only [Pi.smul_apply] at hi
  rw [Matrix.mulVec, dotProduct,
    Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)] at hi
  simp at hi
  rw [← hi]
  simp [Matrix.smul_apply, Matrix.one_apply]

private lemma mem_gluedModule_iff [IsLocalization.Away f Rf]
    [IsLocalization.Away (algebraMap A B f) Bf] (ρ : Rf →ₐ[A] Bf) {n : ℕ}
    (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) (x : Fin n → Rf) (y : Fin n → B) :
    (x, y) ∈ gluedModule A B Rf Bf ρ n g ↔
      g (fun i => ρ (x i)) = fun i => algebraMap B Bf (y i) := by
  unfold gluedModule glueDelta
  simp [LinearMap.mem_ker]
  rw [sub_eq_zero]
  unfold LinearMap.compLeft
  simp only [funext_iff]
  congr!

/-- The first component of an element of the glued module, multiplied by `f ^ K`, comes from
`A ^ n`, and its image in `B ^ n` lies in the image of `W`. -/
private lemma exists_integral_repr [IsLocalization.Away f Rf]
    [IsLocalization.Away (algebraMap A B f) Bf] (hB : IsCompletionLike A f B)
    (hA : IsSMulRegular A f) (hBf : IsSMulRegular B f) {ρ : Rf →ₐ[A] Bf} {n K : ℕ}
    {g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)} {W : Matrix (Fin n) (Fin n) B}
    (hW : ∀ b : Fin n → B, (f ^ K : A) • g.symm (fun i => algebraMap B Bf (b i))
      = fun i => algebraMap B Bf (W.mulVec b i))
    {x : Fin n → Rf} {y : Fin n → B} (hxy : (x, y) ∈ gluedModule A B Rf Bf ρ n g) :
    ∃ a : Fin n → A, ((fun i => algebraMap A Rf (a i)) = (f ^ K : A) • x) ∧
      (fun i => algebraMap A B (a i)) = W.mulVec y := by
  have glue_eq : g (fun i => ρ (x i)) = fun i => algebraMap B Bf (y i) :=
    (mem_gluedModule_iff (f := f) ρ g x y).mp hxy
  have hgy : (fun i => ρ (x i)) = g.symm (fun i => algebraMap B Bf (y i)) := by
    rw [← glue_eq]
    exact (g.symm_apply_apply _).symm
  have hfx : (f ^ K : A) • (fun i => ρ (x i)) = fun i => algebraMap B Bf (W.mulVec y i) := by
    rw [hgy]; exact hW y
  have hfx' : ∀ i, ρ ((f ^ K : A) • x i) = algebraMap B Bf (W.mulVec y i) := by
    intro i
    have hc := congr_fun hfx i
    rw [Pi.smul_apply] at hc
    rw [map_smul]
    exact hc
  choose a ha using fun i => exists_preimage_of_glue hB hA hBf ρ ((f ^ K : A) • x i)
    (W.mulVec y i) (hfx' i)
  refine ⟨a, funext ha, funext fun i => ?_⟩
  have h1 : algebraMap A Bf (a i) = ρ (f ^ K • x i) := by
    rw [← ha i]
    exact (ρ.commutes (a i)).symm
  rw [IsScalarTower.algebraMap_apply A B Bf] at h1
  have h2 : (algebraMap B Bf) ((algebraMap A B) (a i)) = (algebraMap B Bf) ((W.mulVec y) i) := by
    rw [h1, hfx']
  exact injective_algebraMap_Bf hBf h2

/-- The key computation for `exists_decomp`. -/
private lemma image_sub_eq {n κ m : ℕ} (hm : m = 2 * κ)
    {W T : Matrix (Fin n) (Fin n) B} {Wh : Matrix (Fin n) (Fin n) A}
    (hWh : Wh.map (algebraMap A B) = W + (f ^ m : A) • T)
    {a α : Fin n → A} {y y' : Fin n → B}
    (ha : (fun i => algebraMap A B (a i)) = W.mulVec y)
    (hy : y = (fun i => algebraMap A B (α i)) + (f ^ κ : A) • y') :
    (fun i => algebraMap A B ((a - Wh.mulVec α) i))
      = (f ^ κ : A) • (W.mulVec y' - (f ^ κ : A) • T.mulVec (fun i => algebraMap A B (α i))) := by
  subst hm
  funext i
  have hmap : ∀ (M : Matrix (Fin n) (Fin n) A) (v : Fin n → A) (i : Fin n),
      algebraMap A B (M.mulVec v i)
        = (M.map (algebraMap A B)).mulVec (fun j => algebraMap A B (v j)) i :=
    fun M v i => RingHom.map_mulVec (algebraMap A B) M v i
  have hai : algebraMap A B (a i) = W.mulVec y i := congrFun ha i
  simp only [Pi.sub_apply, map_sub, hmap, hWh, hai, hy, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_sub]
  rw [two_mul, pow_add, mul_smul]
  abel

/-- Elements of `L` are of the form `Wh *ᵥ b + f ^ κ • c`. -/
private lemma exists_decomp (hB : IsCompletionLike A f B) {n κ m : ℕ} (hκ : 0 < κ)
    (hm : m = 2 * κ) {W T : Matrix (Fin n) (Fin n) B} {Wh : Matrix (Fin n) (Fin n) A}
    (hWh : Wh.map (algebraMap A B) = W + (f ^ m : A) • T)
    {a : Fin n → A} {y : Fin n → B}
    (ha : (fun i => algebraMap A B (a i)) = W.mulVec y) :
    ∃ b c : Fin n → A, a = Wh.mulVec b + (f ^ κ : A) • c := by
  obtain ⟨α, y', hy⟩ := exists_approx_vec hB hκ y
  obtain ⟨c, hc⟩ := exists_div_vec hB hκ (a - Wh.mulVec α) _ (image_sub_eq hm hWh ha hy)
  exact ⟨α, c, by rw [← hc]; abel⟩

/-- The image in `B ^ n` of `Wh *ᵥ b + f ^ κ • c` lies in the image of `W`. -/
private lemma mem_W_image {n κ m : ℕ} (hm : m = 2 * κ)
    {W V T : Matrix (Fin n) (Fin n) B} {Wh : Matrix (Fin n) (Fin n) A}
    (hWV : W * V = (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) B))
    (hWh : Wh.map (algebraMap A B) = W + (f ^ m : A) • T) (b c : Fin n → A) :
    ∃ u : Fin n → B,
      (fun i => algebraMap A B ((Wh.mulVec b + (f ^ κ : A) • c) i)) = W.mulVec u := by
  let b' : Fin n → B := fun i => algebraMap A B (b i)
  let c' : Fin n → B := fun i => algebraMap A B (c i)
  use b' + f ^ (m - κ) • V.mulVec (T.mulVec b') + V.mulVec c'
  have lhs_eq : (fun i => algebraMap A B ((Wh.mulVec b + f ^ κ • c) i)) =
      (Wh.map (algebraMap A B)).mulVec b' + f ^ κ • c' := by
    ext i
    simp only [Matrix.mulVec, Algebra.smul_def, Pi.add_apply, Pi.smul_apply]
    rw [map_add]
    simp only [dotProduct]
    rw [map_sum]
    congr 1
    · exact Finset.sum_congr rfl fun x _ => by simp [map_mul, Matrix.map_apply, b']
    · simp [c']
  rw [lhs_eq, hWh]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec]
  have WV_mulVec : ∀ v, (W * V).mulVec v = f ^ κ • v := by
    intro v
    rw [hWV]
    simp [Matrix.smul_mulVec, Matrix.one_mulVec]
  have WVT : W * (V * T) = f ^ κ • T := by
    rw [← Matrix.mul_assoc, hWV]
    simp
  simp [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [WV_mulVec, WVT]
  simp [Matrix.smul_mulVec]
  rw [smul_smul, ← pow_add]
  congr 1
  have hκ_le : κ ≤ m := by rw [hm]; omega
  rw [Nat.sub_add_cancel hκ_le]

/-- `f ^ K` acts invertibly on `Rf ^ n`. -/
private lemma exists_smul_pow_eq_Rf [IsLocalization.Away f Rf] {n K : ℕ} (v : Fin n → Rf) :
    ∃ x : Fin n → Rf, (f ^ K : A) • x = v := by
  have hf_unit : IsUnit (algebraMap A Rf f) :=
    IsLocalization.map_units _ (⟨f, 1, pow_one f⟩ : Submonoid.powers f)
  refine ⟨hf_unit.unit⁻¹ ^ K • v, ?_⟩
  ext i
  simp only [Algebra.smul_def]
  simp only [Pi.mul_apply, Pi.smul_apply]
  rw [Pi.algebraMap_apply]
  rw [RingHom.map_pow]
  have heq : (algebraMap A Rf) f ^ K = hf_unit.unit.val ^ K := rfl
  rw [heq]
  have h1 : (hf_unit.unit ^ K : Rf) * (hf_unit.unit⁻¹ ^ K : Rf) = 1 := by
    rw [show (hf_unit.unit ^ K : Rf) = ((hf_unit.unit ^ K) : Rfˣ) from rfl,
      show (hf_unit.unit⁻¹ ^ K : Rf) = ((hf_unit.unit⁻¹ ^ K) : Rfˣ) from rfl, ← Units.val_mul]
    simp
  have h2 : (hf_unit.unit⁻¹ ^ K) • v i = (hf_unit.unit⁻¹ ^ K : Rf) * v i := rfl
  rw [h2, ← mul_assoc, h1, one_mul]

/-- Membership in the glued module, for a pair coming from an integral vector. -/
private lemma mem_gluedModule_of [IsLocalization.Away f Rf]
    [IsLocalization.Away (algebraMap A B f) Bf] (hBf : IsSMulRegular B f)
    {ρ : Rf →ₐ[A] Bf} {n K : ℕ} {g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)}
    {W : Matrix (Fin n) (Fin n) B}
    (hW : ∀ b : Fin n → B, (f ^ K : A) • g.symm (fun i => algebraMap B Bf (b i))
      = fun i => algebraMap B Bf (W.mulVec b i))
    {a : Fin n → A} {u : Fin n → B} {x : Fin n → Rf}
    (ha : (fun i => algebraMap A B (a i)) = W.mulVec u)
    (hx : (f ^ K : A) • x = fun i => algebraMap A Rf (a i)) :
    (x, u) ∈ gluedModule A B Rf Bf ρ n g := by
  rw [gluedModule, LinearMap.mem_ker]
  simp [glueDelta]
  have hρx : (f ^ K : A) • ((ρ.toLinearMap.compLeft (Fin n)) x) =
      fun i => algebraMap A Bf (a i) := by
    have h1 : (ρ.toLinearMap.compLeft (Fin n)) ((f ^ K : A) • x) =
        (ρ.toLinearMap.compLeft (Fin n)) (fun i => algebraMap A Rf (a i)) := by
      rw [hx]
    rw [LinearMap.map_smul_of_tower] at h1
    have h2 : (ρ.toLinearMap.compLeft (Fin n)) (fun i => algebraMap A Rf (a i)) =
        fun i => ρ (algebraMap A Rf (a i)) := rfl
    rw [h2] at h1
    simp [AlgHom.commutes] at h1
    exact h1
  have hg_symm : (f ^ K : A) • g.symm (fun i => algebraMap B Bf (u i)) =
      fun i => algebraMap A Bf (a i) := by
    have h1 := hW u
    rw [ha.symm] at h1
    simp only [← IsScalarTower.algebraMap_apply A B Bf] at h1
    exact h1
  have hboth : (f ^ K : A) • ((ρ.toLinearMap.compLeft (Fin n)) x : Fin n → Bf) =
      (f ^ K : A) • (g.symm (fun i => algebraMap B Bf (u i)) : Fin n → Bf) := by
    rw [hρx, hg_symm]
  have heq : (ρ.toLinearMap.compLeft (Fin n)) x = g.symm (fun i => algebraMap B Bf (u i)) :=
    smul_pow_injective_Bf (A := A) (f := f) (B := B) hboth
  rw [heq]
  simp [LinearEquiv.apply_symm_apply]
  ext i
  simp [IsScalarTower.toAlgHom_apply]

/-- An integral vector whose image in `B ^ n` lies in the image of `W` comes from the glued
module. -/
private lemma exists_glued_of_mem_W_image [IsLocalization.Away f Rf]
    [IsLocalization.Away (algebraMap A B f) Bf] (hBf : IsSMulRegular B f)
    {ρ : Rf →ₐ[A] Bf} {n K : ℕ} {g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)}
    {W : Matrix (Fin n) (Fin n) B}
    (hW : ∀ b : Fin n → B, (f ^ K : A) • g.symm (fun i => algebraMap B Bf (b i))
      = fun i => algebraMap B Bf (W.mulVec b i))
    (a : Fin n → A) (u : Fin n → B)
    (ha : (fun i => algebraMap A B (a i)) = W.mulVec u) :
    ∃ (x : Fin n → Rf) (y : Fin n → B), (x, y) ∈ gluedModule A B Rf Bf ρ n g ∧
      (fun i => algebraMap A Rf (a i)) = (f ^ K : A) • x := by
  obtain ⟨x, hx⟩ := exists_smul_pow_eq_Rf (A := A) (f := f) (Rf := Rf) (K := K)
    (fun i => algebraMap A Rf (a i))
  exact ⟨x, u, mem_gluedModule_of hBf hW ha hx, hx.symm⟩

/-- Conversely, every element of the form `Wh *ᵥ b + f ^ κ • c` arises from the glued module. -/
private lemma exists_glued_of_decomp [IsLocalization.Away f Rf]
    [IsLocalization.Away (algebraMap A B f) Bf] (hBf : IsSMulRegular B f)
    {ρ : Rf →ₐ[A] Bf} {n K κ m : ℕ} (hm : m = 2 * κ)
    {g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)} {V W T : Matrix (Fin n) (Fin n) B}
    {Wh : Matrix (Fin n) (Fin n) A}
    (hWV : W * V = (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) B))
    (hWh : Wh.map (algebraMap A B) = W + (f ^ m : A) • T)
    (hW : ∀ b : Fin n → B, (f ^ K : A) • g.symm (fun i => algebraMap B Bf (b i))
      = fun i => algebraMap B Bf (W.mulVec b i))
    (b c : Fin n → A) :
    ∃ (x : Fin n → Rf) (y : Fin n → B), (x, y) ∈ gluedModule A B Rf Bf ρ n g ∧
      (fun i => algebraMap A Rf ((Wh.mulVec b + (f ^ κ : A) • c) i)) = (f ^ K : A) • x := by
  obtain ⟨u, hu⟩ := mem_W_image hm hWV hWh b c
  exact exists_glued_of_mem_W_image (ρ := ρ) hBf hW _ u hu

/-- The product `Wh * Vh` is `f ^ κ` up to an error divisible by `f ^ m`. -/
private lemma exists_error_matrix (hB : IsCompletionLike A f B) {n κ m : ℕ} (hκ : 0 < κ)
    (hm : m = 2 * κ) {W V T T' : Matrix (Fin n) (Fin n) B} {Wh Vh : Matrix (Fin n) (Fin n) A}
    (hWV : W * V = (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) B))
    (hWh : Wh.map (algebraMap A B) = W + (f ^ m : A) • T)
    (hVh : Vh.map (algebraMap A B) = V + (f ^ m : A) • T') :
    ∃ S : Matrix (Fin n) (Fin n) A,
      Wh * Vh = (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) A) + (f ^ m : A) • S := by
  have hprod : (Wh * Vh).map (algebraMap A B)
      = (W + (f ^ m : A) • T) * (V + (f ^ m : A) • T') := by
    rw [Matrix.map_mul, hWh, hVh]
  have h_expand : (W + (f ^ m : A) • T) * (V + (f ^ m : A) • T') =
      W * V + (f ^ m : A) • (W * T' + T * V) + (f ^ m : A) ^ 2 • (T * T') := by
    simp only [add_mul, mul_add]
    simp
    rw [show (f ^ m : A) • ((f ^ m : A) • (T * T')) = (f ^ m : A) ^ 2 • (T * T') by
      rw [smul_smul]; ring_nf]
    abel
  have hprod' : (Wh * Vh).map (algebraMap A B) =
      (f ^ κ : A) • 1 + (f ^ m : A) • (W * T' + T * V) + (f ^ m : A) ^ 2 • (T * T') := by
    rw [hprod, h_expand, hWV]
  have hprod'' : (Wh * Vh).map (algebraMap A B) =
      (f ^ κ : A) • 1 + (f ^ m : A) • (W * T' + T * V + (f ^ m : A) • (T * T')) := by
    rw [hprod']
    simp [sq, smul_smul]
    abel
  set S' : Matrix (Fin n) (Fin n) B := W * T' + T * V + (f ^ m : A) • (T * T') with hS'
  have hdiff : (Wh * Vh).map (algebraMap A B) - ((f ^ κ : A) • 1) = (f ^ m : A) • S' := by
    rw [hprod'']; abel
  have hm_pos : 0 < m := by rw [hm]; exact Nat.mul_pos zero_lt_two hκ
  have hideal : Ideal.map (algebraMap A B) (Ideal.span {f ^ m})
      = Ideal.span {(algebraMap A B) (f ^ m)} := by
    rw [Ideal.map_span]
    simp [Set.image_singleton]
  have hker' := hB.ker_mod m hm_pos
  have hmem : ∀ i j,
      (Wh * Vh - (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) A)) i j ∈ Ideal.span {f ^ m} := by
    intro i j
    have h1 := congr_fun₂ hdiff i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] at h1
    have h2 : (Wh * Vh - (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) A)) i j =
        (Wh * Vh) i j - (f ^ κ : A) • (if i = j then (1 : A) else 0) := rfl
    rw [h2]
    have h3' : (algebraMap A B) ((Wh * Vh) i j - (f ^ κ : A) • (if i = j then (1 : A) else 0)) =
        (algebraMap A B) ((Wh * Vh) i j)
          - (algebraMap A B) (f ^ κ • (if i = j then (1 : A) else 0)) := by
      rw [map_sub]
    have h4' : (algebraMap A B) (f ^ κ • (if i = j then (1 : A) else 0)) =
        (algebraMap A B f) ^ κ * (if i = j then (1 : B) else 0) := by
      simp; split_ifs <;> simp
    have h1' : (algebraMap A B) ((Wh * Vh) i j)
        - (algebraMap A B f) ^ κ * (if i = j then (1 : B) else 0) =
        (algebraMap A B f) ^ m * S' i j := by convert h1 using 1 <;> simp [Algebra.smul_def]
    have hine : (algebraMap A B) ((Wh * Vh) i j - (f ^ κ : A) • (if i = j then (1 : A) else 0)) ∈
        Ideal.map (algebraMap A B) (Ideal.span {f ^ m}) := by
      rw [h3', h4', h1', hideal, ← map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    exact hker'.symm ▸ RingHom.mem_ker.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr hine)
  choose S hS using fun i j => Ideal.mem_span_singleton.mp (hmem i j)
  refine ⟨S, ?_⟩
  ext i j
  have h := hS i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply] at h ⊢
  rw [sub_eq_iff_eq_add] at h
  convert h using 1
  ring_nf
  simp
  rw [add_comm]

/-- Division by `f ^ κ` is possible on the image of `Vh`. -/
private lemma exists_half {n κ m : ℕ} (hm : m = 2 * κ) {Wh Vh S' : Matrix (Fin n) (Fin n) A}
    (h2 : Vh * Wh = (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) A) + (f ^ m : A) • S')
    (b c : Fin n → A) :
    ∃ p : Fin n → A, (f ^ κ : A) • p = Vh.mulVec (Wh.mulVec b + (f ^ κ : A) • c) := by
  use b + Vh.mulVec c + f ^ κ • S'.mulVec b
  rw [Matrix.mulVec_add, Matrix.mulVec_smul]
  have h3 : Vh.mulVec (Wh.mulVec b) = (Vh * Wh).mulVec b := Matrix.mulVec_mulVec _ _ _
  rw [h3, h2]
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [smul_smul, ← pow_add]
  rw [show κ + κ = m by rw [hm]; ring]
  abel

/-- The section identity. -/
private lemma split_identity {n κ m : ℕ} (hm : m = 2 * κ) (hA : IsSMulRegular A f)
    {Wh Vh S : Matrix (Fin n) (Fin n) A}
    (h1 : Wh * Vh = (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) A) + (f ^ m : A) • S)
    {a p : Fin n → A} (hp : (f ^ κ : A) • p = Vh.mulVec a) :
    Wh.mulVec p + (f ^ κ : A) • (-(S.mulVec a)) = a := by
  have eq1 : Wh.mulVec (Vh.mulVec a) = (Wh * Vh).mulVec a := Matrix.mulVec_mulVec _ _ _
  rw [h1, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at eq1
  have eq2 : Wh.mulVec (Vh.mulVec a) = (f ^ κ : A) • Wh.mulVec p := by
    rw [hp.symm]
    exact Matrix.mulVec_smul _ _ _
  rw [eq2] at eq1
  have hm' : (f ^ m : A) = (f ^ κ : A) * (f ^ κ : A) := by
    rw [hm]; simp [pow_mul']; ring
  rw [Matrix.smul_mulVec, hm', mul_smul] at eq1
  have eq3 : (f ^ κ : A) • (Wh.mulVec p - a - (f ^ κ : A) • S.mulVec a) = 0 := by
    rw [smul_sub, smul_sub, eq1]
    abel
  have hreg := IsSMulRegular.pow κ hA
  have eq4 : Wh.mulVec p - a - (f ^ κ : A) • S.mulVec a = 0 := by
    ext i
    have hi := congrFun eq3 i
    rw [Pi.smul_apply, smul_eq_mul] at hi
    simp at hi
    rw [← mul_zero (f ^ κ)] at hi
    simp [hreg hi]
  rw [smul_neg]
  linear_combination eq4

/-- The embedding of the glued module into `A ^ n` is injective. -/
private lemma glued_eq_zero [IsLocalization.Away f Rf]
    [IsLocalization.Away (algebraMap A B f) Bf] (hBf : IsSMulRegular B f)
    {ρ : Rf →ₐ[A] Bf} {n K : ℕ} {g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)}
    {x : Fin n → Rf} {y : Fin n → B} (hxy : (x, y) ∈ gluedModule A B Rf Bf ρ n g)
    (h : (f ^ K : A) • x = 0) : x = 0 ∧ y = 0 := by
  have hx : x = 0 := by
    have hf_unit : IsUnit (algebraMap A Rf f) :=
      IsLocalization.map_units (S := Rf) ⟨f, Submonoid.mem_powers f⟩
    have hfu : IsUnit ((algebraMap A Rf) (f ^ K)) := by rw [map_pow]; exact hf_unit.pow K
    ext i
    have hi : (algebraMap A Rf) (f ^ K) * x i = 0 := by
      have := congr_fun h i
      simp only [Pi.smul_apply, Algebra.smul_def] at this
      exact this
    exact hfu.mul_left_cancel (by simpa using hi)
  have hy : y = 0 := by
    have hg : glueDelta A B Rf Bf ρ n g (x, y) = 0 := hxy
    rw [glueDelta] at hg
    simp only [LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply] at hg
    have heq : g ((fun i => ρ (x i)) : Fin n → Bf) = (fun i => algebraMap B Bf (y i)) :=
      sub_eq_zero.mp hg
    simp [hx] at heq
    have h0 : (fun _ => (0 : Bf)) = (0 : Fin n → Bf) := rfl
    rw [h0, g.map_zero] at heq
    ext i
    have := congr_fun heq i
    simp at this
    have heq' : (algebraMap B Bf) (y i) = (algebraMap B Bf) 0 := by simp [this.symm]
    exact injective_algebraMap_Bf hBf heq'
  exact ⟨hx, hy⟩

end Aux

/-- The glued module of a rank-`n` gluing datum is finite projective over `A`
(Stacks 0BP2 / 0BP6: the vector-bundle case of Beauville-Laszlo). -/
theorem gluedModule_finite_projective
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (hA : IsSMulRegular A f) (hBf : IsSMulRegular B f)
    (Rf : Type u) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    [IsLocalization.Away (algebraMap A B f) Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf)) :
    Module.Finite A ↥(gluedModule A B Rf Bf ρ n g) ∧
      Module.Projective A ↥(gluedModule A B Rf Bf ρ n g) := by
  classical
  -- common denominators for `g` and `g⁻¹`
  obtain ⟨K₁, hK₁⟩ := exists_denominator_matrix (A := A) (f := f) (B := B) g.toLinearMap
  obtain ⟨K₂, hK₂⟩ := exists_denominator_matrix (A := A) (f := f) (B := B) g.symm.toLinearMap
  obtain ⟨V, hV⟩ := hK₁ (max K₁ K₂ + 1) (le_trans (le_max_left _ _) (Nat.le_succ _))
  obtain ⟨W, hW⟩ := hK₂ (max K₁ K₂ + 1) (le_trans (le_max_right _ _) (Nat.le_succ _))
  set K := max K₁ K₂ + 1 with hKdef
  set κ := 2 * K with hκdef
  set m := 2 * κ with hmdef
  have hκpos : 0 < κ := by omega
  have hmpos : 0 < m := by omega
  have hWV : W * V = (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) B) :=
    matrix_mul_eq_pow hBf hV hW
  have hVW : V * W = (f ^ κ : A) • (1 : Matrix (Fin n) (Fin n) B) :=
    matrix_mul_eq_pow (g := g.symm) hBf hW (by simpa using hV)
  obtain ⟨Wh, T, hWh⟩ := exists_lift_matrix hB hmpos W
  obtain ⟨Vh, T', hVh⟩ := exists_lift_matrix hB hmpos V
  obtain ⟨S, h1⟩ := exists_error_matrix hB hκpos hmdef hWV hWh hVh
  obtain ⟨S', h2⟩ := exists_error_matrix hB hκpos hmdef hVW hVh hWh
  -- the structure map `A ^ n → Rf ^ n`
  set ψ : (Fin n → A) →ₗ[A] (Fin n → Rf) := (Algebra.linearMap A Rf).compLeft (Fin n) with hψdef
  have hψ : Function.Injective ψ := by
    intro a a' h
    exact funext fun i => injective_algebraMap_Rf (Rf := Rf) hA (congrFun h i)
  -- the map `M → Rf ^ n`, `z ↦ f ^ K • z.1`
  set φ : ↥(gluedModule A B Rf Bf ρ n g) →ₗ[A] (Fin n → Rf) :=
    (f ^ K : A) • (gluedFst A B Rf Bf ρ n g) with hφdef
  have hφapp : ∀ (x : Fin n → Rf) (y : Fin n → B)
      (hxy : (x, y) ∈ gluedModule A B Rf Bf ρ n g), φ ⟨(x, y), hxy⟩ = (f ^ K : A) • x := by
    intro x y hxy; rfl
  have hφ : ∀ z, ∃ a, ψ a = φ z := by
    rintro ⟨⟨x, y⟩, hxy⟩
    obtain ⟨a, ha, -⟩ := exists_integral_repr hB hA hBf hW hxy
    exact ⟨a, by rw [hφapp x y hxy]; exact ha⟩
  obtain ⟨E, hE⟩ := exists_factor ψ hψ φ hφ
  -- `E` is injective
  have hEinj : Function.Injective E := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨x, y⟩, hxy⟩ hz
    have hzero : (f ^ K : A) • x = 0 := by
      have h := hE ⟨(x, y), hxy⟩
      rw [hz, hφapp x y hxy, map_zero] at h
      exact h.symm
    obtain ⟨hx, hy⟩ := glued_eq_zero hBf hxy hzero
    simp [Subtype.ext_iff, Prod.ext_iff, hx, hy]
  -- `E z` decomposes
  have hEdecomp : ∀ z, ∃ b c : Fin n → A, E z = Wh.mulVec b + (f ^ κ : A) • c := by
    rintro ⟨⟨x, y⟩, hxy⟩
    obtain ⟨a, ha, ha'⟩ := exists_integral_repr hB hA hBf hW hxy
    have hEa : E ⟨(x, y), hxy⟩ = a := by
      apply hψ
      rw [hE, hφapp x y hxy]
      exact ha.symm
    rw [hEa]
    exact exists_decomp hB hκpos hmdef hWh ha'
  -- division by `f ^ κ`
  set sc : (Fin n → A) →ₗ[A] (Fin n → A) := LinearMap.lsmul A (Fin n → A) (f ^ κ) with hscdef
  have hsc : Function.Injective sc := by
    intro a a' h
    exact funext fun i => (hA.pow κ) (congrFun h i)
  have hPside : ∀ z, ∃ p, sc p = (Vh.mulVecLin ∘ₗ E) z := by
    intro z
    obtain ⟨b, c, hbc⟩ := hEdecomp z
    obtain ⟨p, hp⟩ := exists_half hmdef h2 b c
    exact ⟨p, by simpa [hscdef, hbc] using hp⟩
  obtain ⟨Pm, hPm⟩ := exists_factor sc hsc (Vh.mulVecLin ∘ₗ E) hPside
  -- the retraction
  set t : ((Fin n → A) × (Fin n → A)) →ₗ[A] (Fin n → A) :=
    Wh.mulVecLin ∘ₗ (LinearMap.fst A (Fin n → A) (Fin n → A)) +
      sc ∘ₗ (LinearMap.snd A (Fin n → A) (Fin n → A)) with htdef
  have hrside : ∀ p, ∃ z, E z = t p := by
    rintro ⟨b, c⟩
    obtain ⟨x, y, hxy, hxa⟩ :=
      exists_glued_of_decomp (ρ := ρ) hBf hmdef hWV hWh hW b c
    refine ⟨⟨(x, y), hxy⟩, ?_⟩
    apply hψ
    rw [hE, hφapp x y hxy, ← hxa]
    funext i
    simp [htdef, hψdef, hscdef, Algebra.smul_def]
  obtain ⟨rr, hrr⟩ := exists_factor E hEinj t hrside
  refine finite_projective_of_split (Pm.prod (-(S.mulVecLin ∘ₗ E))) rr ?_
  intro z
  apply hEinj
  rw [hrr]
  have := split_identity hmdef hA h1 (hPm z)
  simpa [htdef, hscdef] using this
/- ===== node D13 (D13_a2): verified by Aristotle ===== -/
/-! ### Auxiliary constructions for the proof of `glued_unique` -/

/-- The `A`-linear equivalence `N ⊗[A] B ≃ (Fin n → B)` induced by a base change map `v`. -/
private noncomputable def bcEquiv (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ)
    (v : N →ₗ[A] (Fin n → B)) (hv : IsBaseChange B v) :
    N ⊗[A] B ≃ₗ[A] (Fin n → B) :=
  (TensorProduct.comm A N B).trans (hv.equiv.restrictScalars A)

private lemma bcEquiv_apply_toTensor (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ)
    (v : N →ₗ[A] (Fin n → B)) (hv : IsBaseChange B v) (x : N) :
    bcEquiv A B N n v hv (toTensor A B N x) = v x := by
  simp [bcEquiv, toTensor, IsBaseChange.equiv_tmul]

/-- The composite `N ⊗[A] B ≃ (Fin n → B) → (Fin n → Bf)`. -/
private noncomputable def bfMap (A : Type u) [CommRing A]
    (B : Type u) [CommRing B] [Algebra A B]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ)
    (v : N →ₗ[A] (Fin n → B)) (hv : IsBaseChange B v) :
    N ⊗[A] B →ₗ[A] (Fin n → Bf) :=
  ((IsScalarTower.toAlgHom A B Bf).toLinearMap.compLeft (Fin n)).comp
    (bcEquiv A B N n v hv).toLinearMap

/-- Componentwise, `(Fin n → Bf)` is the localization of `(Fin n → B)` at the powers of `f`. -/
private lemma isLocalizedModule_compLeft (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    [IsLocalization.Away (algebraMap A B f) Bf] (n : ℕ) :
    IsLocalizedModule (Submonoid.powers f)
      ((IsScalarTower.toAlgHom A B Bf).toLinearMap.compLeft (Fin n)) := by
  have h : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) Bf := by
    rw [Algebra.algebraMapSubmonoid_powers]; infer_instance
  exact IsLocalizedModule.pi (S := Submonoid.powers f)
    (fun _ : Fin n => (IsScalarTower.toAlgHom A B Bf).toLinearMap)

/-- Hence `(Fin n → Bf)` is the localization of `N ⊗[A] B` at the powers of `f`. -/
private lemma isLocalizedModule_bfMap (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    [IsLocalization.Away (algebraMap A B f) Bf]
    (N : Type u) [AddCommGroup N] [Module A N] (n : ℕ)
    (v : N →ₗ[A] (Fin n → B)) (hv : IsBaseChange B v) :
    IsLocalizedModule (Submonoid.powers f) (bfMap A B Bf N n v hv) := by
  haveI := isLocalizedModule_compLeft A f B Bf n
  exact IsLocalizedModule.of_linearEquiv_right (Submonoid.powers f)
    ((IsScalarTower.toAlgHom A B Bf).toLinearMap.compLeft (Fin n)) (bcEquiv A B N n v hv)

/-- The key commuting square: under the identifications `Φ`, `bcEquiv`, `Θ`, the second map
of the Beauville-Laszlo square for `N` becomes the gluing defect map. -/
private lemma key_comm (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf))
    (N : Type u) [AddCommGroup N] [Module A N]
    (u : N →ₗ[A] (Fin n → Rf)) (v : N →ₗ[A] (Fin n → B)) (hv : IsBaseChange B v)
    (hcompat : (glueDelta A B Rf Bf ρ n g).comp (u.prod v) = 0)
    (Φ : LocalizedModule (Submonoid.powers f) N →ₗ[A] (Fin n → Rf))
    (hΦ : ∀ x : N, Φ (LocalizedModule.mk x 1) = u x)
    (Θ : LocalizedModule (Submonoid.powers f) (N ⊗[A] B) →ₗ[A] (Fin n → Bf))
    (hΘ : ∀ t : N ⊗[A] B, Θ (LocalizedModule.mk t 1) = bfMap A B Bf N n v hv t)
    (hunit : ∀ s : Submonoid.powers f,
      IsUnit ((algebraMap A (Module.End A (Fin n → Bf))) (s : A))) :
    Θ.comp (sqSnd A f B N) =
      (glueDelta A B Rf Bf ρ n g).comp
        (Φ.prodMap (bcEquiv A B N n v hv).toLinearMap) := by
  have h1 : (Θ.comp ((LocalizedModule.map (Submonoid.powers f)
        (toTensor A B N)).restrictScalars A)) =
      ((g.toLinearMap.restrictScalars A).comp (ρ.toLinearMap.compLeft (Fin n))).comp Φ := by
    apply IsLocalizedModule.ext (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) N) hunit
    ext x
    have hx := congrArg (fun L => L x) hcompat
    simp only [LinearMap.comp_apply, LinearMap.prod_apply, Pi.prod, LinearMap.zero_apply,
      glueDelta, LinearMap.sub_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      sub_eq_zero] at hx
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LocalizedModule.mkLinearMap_apply, LocalizedModule.map_mk, hΘ, hΦ, bfMap,
      bcEquiv_apply_toTensor, LinearEquiv.coe_coe]
    rw [← hx]
    rfl
  refine LinearMap.ext fun p => ?_
  obtain ⟨a, b⟩ := p
  have ha := congrArg (fun L => L a) h1
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply] at ha
  simp only [LinearMap.comp_apply, sqSnd, LinearMap.sub_apply, LinearMap.fst_apply,
    LinearMap.snd_apply, map_sub, LinearMap.restrictScalars_apply,
    LocalizedModule.mkLinearMap_apply, hΘ, LinearMap.prodMap_apply, glueDelta,
    LinearEquiv.coe_coe, bfMap]
  rw [ha]
  rfl

/-- Injectivity part of `glued_unique`. -/
private lemma glued_unique_injective (A : Type u) [CommRing A] (f : A)
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (B : Type u) [CommRing B] [Algebra A B] (n : ℕ)
    (N : Type u) [AddCommGroup N] [Module A N] (hN : IsSMulRegular N f)
    (u : N →ₗ[A] (Fin n → Rf)) (hu : IsLocalizedModule (Submonoid.powers f) u)
    (v : N →ₗ[A] (Fin n → B)) :
    Function.Injective (u.prod v) := by
  haveI := hu
  have hinj : Function.Injective u := by
    rw [IsLocalizedModule.injective_iff_isRegular (S := Submonoid.powers f)]
    rintro ⟨c, k, rfl⟩
    exact hN.pow k
  intro x y hxy
  exact hinj (congrArg Prod.fst hxy)

/-- Range part of `glued_unique`. -/
private lemma glued_unique_range
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (Rf : Type u) [CommRing Rf] [Algebra A Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    [IsLocalization.Away (algebraMap A B f) Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf))
    (N : Type u) [AddCommGroup N] [Module A N]
    (u : N →ₗ[A] (Fin n → Rf)) (hu : IsLocalizedModule (Submonoid.powers f) u)
    (v : N →ₗ[A] (Fin n → B)) (hv : IsBaseChange B v)
    (hcompat : (glueDelta A B Rf Bf ρ n g).comp (u.prod v) = 0)
    (hexact : Function.Exact (sqFst A f B N) (sqSnd A f B N)) :
    Set.range (u.prod v) = ↑(gluedModule A B Rf Bf ρ n g) := by
  haveI := hu
  haveI := isLocalizedModule_bfMap A f B Bf N n v hv
  set Phi := IsLocalizedModule.iso (Submonoid.powers f) u with hPhi_def
  set Theta := IsLocalizedModule.iso (Submonoid.powers f) (bfMap A B Bf N n v hv) with hTheta_def
  have hPhi : ∀ x : N, Phi.toLinearMap (LocalizedModule.mk x 1) = u x := by
    intro x; simp [hPhi_def]
  have hTheta : ∀ t : N ⊗[A] B,
      Theta.toLinearMap (LocalizedModule.mk t 1) = bfMap A B Bf N n v hv t := by
    intro t; simp [hTheta_def]
  have hunit := IsLocalizedModule.map_units (S := Submonoid.powers f) (bfMap A B Bf N n v hv)
  have hk := key_comm A f B Rf Bf ρ n g N u v hv hcompat Phi.toLinearMap hPhi
    Theta.toLinearMap hTheta hunit
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    have := congrArg (fun L => L x) hcompat
    simpa [gluedModule, LinearMap.mem_ker] using this
  · rintro p hp
    have hp' : glueDelta A B Rf Bf ρ n g p = 0 := hp
    obtain ⟨p1, p2⟩ := p
    set a := Phi.symm p1 with ha
    set b := (bcEquiv A B N n v hv).symm p2 with hb
    have h0 : Theta (sqSnd A f B N (a, b)) = 0 := by
      have h := congrArg (fun L => L (a, b)) hk
      simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, LinearEquiv.coe_coe] at h
      rw [h, ha, hb]
      simpa using hp'
    have h1 : sqSnd A f B N (a, b) = 0 := by
      apply Theta.injective
      simpa using h0
    obtain ⟨z, hz⟩ := (hexact (a, b)).mp h1
    refine ⟨z, ?_⟩
    have hz1 : LocalizedModule.mk z 1 = a := congrArg Prod.fst hz
    have hz2 : toTensor A B N z = b := congrArg Prod.snd hz
    have hu1 : u z = p1 := by
      rw [← hPhi z, hz1, ha]; simp
    have hv1 : v z = p2 := by
      rw [← bcEquiv_apply_toTensor A B N n v hv z, hz2, hb]; simp
    simp [LinearMap.prod_apply, Pi.prod, hu1, hv1]

/-- Uniqueness of gluing: an `f`-regular `N` with structure maps compatible with the
gluing datum maps isomorphically onto the glued module.  `hA1` is the statement of the
abstract Stage A1 short exactness (assembled from nodes D01-D05). -/
theorem glued_unique
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (hA : IsSMulRegular A f) (hBf : IsSMulRegular B f)
    (Rf : Type u) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    [IsLocalization.Away (algebraMap A B f) Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf))
    (N : Type u) [AddCommGroup N] [Module A N] (hN : IsSMulRegular N f)
    (u : N →ₗ[A] (Fin n → Rf)) (hu : IsLocalizedModule (Submonoid.powers f) u)
    (v : N →ₗ[A] (Fin n → B)) (hv : IsBaseChange B v)
    (hcompat : (glueDelta A B Rf Bf ρ n g).comp (u.prod v) = 0)
    (hA1 : ∀ (P : Type u) [AddCommGroup P] [Module A P], IsSMulRegular P f →
      Function.Injective (sqFst A f B P) ∧
        Function.Exact (sqFst A f B P) (sqSnd A f B P) ∧
        Function.Surjective (sqSnd A f B P)) :
    Function.Injective (u.prod v) ∧
      Set.range (u.prod v) = ↑(gluedModule A B Rf Bf ρ n g) :=
  ⟨glued_unique_injective A f Rf B n N hN u hu v,
    glued_unique_range A f B Rf Bf ρ n g N u hu v hv hcompat (hA1 N hN).2.1⟩

/- ===================== headline theorems (Stage A) ===================== -/
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
  have hB : IsCompletionLike A f (AdicCompletion (Ideal.span {f}) A) :=
    isCompletionLike_adicCompletion A f
  have hBf : IsSMulRegular (AdicCompletion (Ideal.span {f}) A) f :=
    isSMulRegular_adicCompletion A f hA
  refine ⟨sqFst_injective A f _ M hM, ?_, sqSnd_surjective A f _ hB M⟩
  exact sq_exact_of_smulRegular_baseChange A f _ hB M hM
    (isSMulRegular_baseChange A f _ hB hA hBf M hM)
    (fun n hn => quotSMulTop_baseChange_bijective A f _ hB M n hn)

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
  have hB : IsCompletionLike A f (AdicCompletion (Ideal.span {f}) A) :=
    isCompletionLike_adicCompletion A f
  have hBf : IsSMulRegular (AdicCompletion (Ideal.span {f}) A) f :=
    isSMulRegular_adicCompletion A f hA
  have hfp := gluedModule_finite_projective A f _ hB hA hBf Rf Bf ρ n g
  exact ⟨hfp.1, hfp.2, gluedFst_isLocalizedModule A f _ hB hA hBf Rf Bf ρ n g,
    gluedSnd_isBaseChange A f _ hB hA hBf Rf Bf ρ n g⟩

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
  have hB : IsCompletionLike A f (AdicCompletion (Ideal.span {f}) A) :=
    isCompletionLike_adicCompletion A f
  have hBf : IsSMulRegular (AdicCompletion (Ideal.span {f}) A) f :=
    isSMulRegular_adicCompletion A f hA
  exact glued_unique A f _ hB hA hBf Rf Bf ρ n g N hN u hu v hv hcompat
    (fun P _ _ hP => beauvilleLaszlo_arithmeticSquare_exact A f hA P hP)

end BeauvilleLaszlo
