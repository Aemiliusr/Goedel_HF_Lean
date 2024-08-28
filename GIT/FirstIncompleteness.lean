import GIT.Sigma

open FirstOrder Language

suppress_compilation

namespace HF

theorem first_incompleteness (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) :
    ∃ (δ : Lang.Sentence), (¬ ⊢ δ) ∧ (¬ ⊢ ∼δ) ∧ stdModel ⊧ δ := sorry

end HF
