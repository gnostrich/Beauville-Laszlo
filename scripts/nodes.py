"""Frozen lemma DAG for the Beauville-Laszlo Aristotle campaign.

Each node is a self-contained Lean file: the shared preamble (extracted verbatim
from BeauvilleLaszlo/Challenge.lean between the PREAMBLE markers) plus one target
theorem stated with `sorry`.  Dependencies on other nodes are passed as explicit
hypothesis arguments, so every node is independent and can run in parallel.

Assembly of the headline theorems from proved nodes is glue, not a node.
"""

from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
CHALLENGE = REPO / "BeauvilleLaszlo" / "Challenge.lean"

HEADER = """/-
Beauville-Laszlo campaign node. Self-contained: shared preamble + one target theorem.
Prove the final theorem (the one ending in `sorry`). Do not change any statement.
-/
import Mathlib

open scoped TensorProduct

namespace BeauvilleLaszlo

universe u
"""

FOOTER = "\nend BeauvilleLaszlo\n"


def preamble() -> str:
    text = CHALLENGE.read_text()
    start = text.index("-- PREAMBLE START")
    end = text.index("-- PREAMBLE END")
    return text[start + len("-- PREAMBLE START"):end].strip()


# ---------------------------------------------------------------------------
# Node targets.  {id: (short description, Lean theorem text with sorry)}
# ---------------------------------------------------------------------------

NODES: dict[str, tuple[str, str]] = {}

NODES["H0"] = ("calibration: localization map injective on f-regular module", """
/-- Calibration lemma (harness validity cell H0): if `f` is regular on `M`, the
localization map `M → M_f` is injective.  Known short Mathlib proof. -/
theorem calibration_localization_injective
    (A : Type u) [CommRing A] (f : A)
    (M : Type u) [AddCommGroup M] [Module A M] (hM : IsSMulRegular M f) :
    Function.Injective (LocalizedModule.mkLinearMap (Submonoid.powers f) M) := by
  sorry
""")

NODES["D01"] = ("injectivity of sqFst for f-regular M", """
/-- Left exactness of the Beauville-Laszlo square: for `f`-regular `M`, the map
`M → M_f × (M ⊗ B)` is injective (already via the first component). -/
theorem sqFst_injective
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (M : Type u) [AddCommGroup M] [Module A M] (hM : IsSMulRegular M f) :
    Function.Injective (sqFst A f B M) := by
  sorry
""")

NODES["D02"] = ("surjectivity of sqSnd (right exactness, any M)", """
/-- Right exactness of the Beauville-Laszlo square holds for every module `M`
(Stacks 0BNI: uses only surjectivity of `A → B/f^nB`). -/
theorem sqSnd_surjective
    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (M : Type u) [AddCommGroup M] [Module A M] :
    Function.Surjective (sqSnd A f B M) := by
  sorry
""")

NODES["D03"] = ("mod-f^n base change: M/f^nM = (M x B)/f^n(M x B)", """
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
  sorry
""")

NODES["D04"] = ("middle exactness given f-regularity of M x B", """
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
  sorry
""")

NODES["D05"] = ("f-regularity survives base change (the deep BL input)", """
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
  sorry
""")

NODES["D07"] = ("f-adic completion is completion-like (Stacks 0BNJ)", """
/-- Stacks Tag 0BNJ: for any commutative ring `A` and `f : A`, the `f`-adic completion
satisfies the completion-like property: `A/f^n → Â/f^nÂ` is bijective for `n ≥ 1`. -/
theorem isCompletionLike_adicCompletion
    (A : Type u) [CommRing A] (f : A) :
    IsCompletionLike A f (AdicCompletion (Ideal.span {f}) A) := by
  sorry
""")

NODES["D08"] = ("f nzd on A implies f nzd on the completion", """
/-- If `f` is a non-zerodivisor on `A`, it is a non-zerodivisor on the `f`-adic
completion of `A` (Stacks 0BNI region, cf. 0BNS remark). -/
theorem isSMulRegular_adicCompletion
    (A : Type u) [CommRing A] (f : A) (hA : IsSMulRegular A f) :
    IsSMulRegular (AdicCompletion (Ideal.span {f}) A) f := by
  sorry
""")

_A2_CTX = """    (A : Type u) [CommRing A] (f : A)
    (B : Type u) [CommRing B] [Algebra A B]
    (hB : IsCompletionLike A f B)
    (hA : IsSMulRegular A f) (hBf : IsSMulRegular B f)
    (Rf : Type u) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf]
    (Bf : Type u) [CommRing Bf] [Algebra A Bf] [Algebra B Bf] [IsScalarTower A B Bf]
    [IsLocalization.Away (algebraMap A B f) Bf]
    (ρ : Rf →ₐ[A] Bf) (n : ℕ) (g : (Fin n → Bf) ≃ₗ[Bf] (Fin n → Bf))"""

NODES["D10"] = ("glued module localizes to the Rf-side free module", """
/-- The first projection exhibits `(Fin n → Rf)` as the localization of the glued
module at the powers of `f`. -/
theorem gluedFst_isLocalizedModule
""" + _A2_CTX + """ :
    IsLocalizedModule (Submonoid.powers f) (gluedFst A B Rf Bf ρ n g) := by
  sorry
""")

NODES["D11"] = ("glued module base-changes to the B-side free module", """
/-- The second projection exhibits `(Fin n → B)` as the base change of the glued
module along `A → B`. -/
theorem gluedSnd_isBaseChange
""" + _A2_CTX + """ :
    IsBaseChange B (gluedSnd A B Rf Bf ρ n g) := by
  sorry
""")

NODES["D12"] = ("glued module is finite projective (BL existence crux)", """
/-- The glued module of a rank-`n` gluing datum is finite projective over `A`
(Stacks 0BP2 / 0BP6: the vector-bundle case of Beauville-Laszlo). -/
theorem gluedModule_finite_projective
""" + _A2_CTX + """ :
    Module.Finite A ↥(gluedModule A B Rf Bf ρ n g) ∧
      Module.Projective A ↥(gluedModule A B Rf Bf ρ n g) := by
  sorry
""")

NODES["D13"] = ("uniqueness: any compatible f-regular N maps isomorphically", """
/-- Uniqueness of gluing: an `f`-regular `N` with structure maps compatible with the
gluing datum maps isomorphically onto the glued module.  `hA1` is the statement of the
abstract Stage A1 short exactness (assembled from nodes D01-D05). -/
theorem glued_unique
""" + _A2_CTX + """
    (N : Type u) [AddCommGroup N] [Module A N] (hN : IsSMulRegular N f)
    (u : N →ₗ[A] (Fin n → Rf)) (hu : IsLocalizedModule (Submonoid.powers f) u)
    (v : N →ₗ[A] (Fin n → B)) (hv : IsBaseChange B v)
    (hcompat : (glueDelta A B Rf Bf ρ n g).comp (u.prod v) = 0)
    (hA1 : ∀ (P : Type u) [AddCommGroup P] [Module A P], IsSMulRegular P f →
      Function.Injective (sqFst A f B P) ∧
        Function.Exact (sqFst A f B P) (sqSnd A f B P) ∧
        Function.Surjective (sqSnd A f B P)) :
    Function.Injective (u.prod v) ∧
      Set.range (u.prod v) = ↑(gluedModule A B Rf Bf ρ n g) := by
  sorry
""")

DAG_ORDER = ["D01", "D02", "D03", "D04", "D05", "D07", "D08", "D10", "D11", "D12", "D13"]


def node_file(node_id: str) -> str:
    _, body = NODES[node_id]
    return HEADER + "\n" + preamble() + "\n\n" + body.strip() + "\n" + FOOTER


if __name__ == "__main__":
    import sys
    out = REPO / "aristotle_runs" / "nodefiles"
    out.mkdir(parents=True, exist_ok=True)
    ids = sys.argv[1:] or ["H0", *DAG_ORDER]
    for nid in ids:
        p = out / f"{nid}.lean"
        p.write_text(node_file(nid))
        print(f"wrote {p}")
