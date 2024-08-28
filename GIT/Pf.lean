import GIT.Sigma

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

namespace IsSigma

abbrev Pf : Lang.Formula (Fin 1) := sorry

end IsSigma

theorem prf_iff_prf_Pf_code (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) [Fintype α]
        (φ : Lang.BoundedFormula α n) : ⊢ φ ↔ ⊢ (subst Pf ![(Code.Formula φ).1]) := sorry

end HF
