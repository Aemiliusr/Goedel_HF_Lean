import GIT.Sigma

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

namespace IsSigma

abbrev Pf : Lang.Formula (Fin 1) := sorry

end IsSigma

lemma Pf_isSigma [Fintype α] (φ : Lang.BoundedFormula α n) :
    IsSigma (subst IsSigma.Pf ![(Code.Formula φ).1]) := sorry

theorem prf_iff_prf_Pf_code (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) [Fintype α]
    (φ : Lang.BoundedFormula α n) : ⊢ φ ↔ ⊢ (subst IsSigma.Pf ![(Code.Formula φ).1]) := sorry

end HF
