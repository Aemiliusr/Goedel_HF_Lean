import GIT.Pf

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

theorem diagonal (α : Lang.Formula (Fin 1)) : ∃ (δ : Lang.Sentence),
    ⊢ δ ⇔ (subst α ![(Code.Formula δ).1]) := sorry

theorem first_incompleteness (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) :
    ∃ (δ : Lang.Sentence), (¬ ⊢ δ) ∧ (¬ ⊢ ∼δ) ∧ stdModel ⊧ δ := by
  obtain ⟨δ, hδ⟩ := diagonal ∼IsSigma.Pf
  use δ
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · by_contra prf
    apply prf_iff_prf_of_prf_iff at hδ
    rw [hδ] at prf
    rw [prf_iff_prf_Pf_code cons] at hδ
    apply cons
    use subst IsSigma.Pf ![(Code.Formula δ).1]
    aesop
  · by_contra prf
    apply prf_neg_iff_of_prf_iff at hδ
    apply prf_iff_prf_of_prf_iff at hδ
    have : ⊢ (subst IsSigma.Pf ![(Code.Formula δ).1]) := by apply prf_of_prf_neg_neg; aesop
    rw [← prf_iff_prf_Pf_code cons] at this
    apply cons
    use δ
  · by_contra h; have h2 := h
    rw [neg_models_iff_models_neg_of_sentence] at h
    apply prf_neg_iff_of_prf_iff at hδ
    have models : stdModel ⊧ (subst IsSigma.Pf ![(Code.Formula δ).1]) := by
      rwa [stdModel.models_iff_of_prf_iff cons (subst IsSigma.Pf ![(Code.Formula δ).1]) ∼δ]
      rw [completeness] at *
      intro S _ v xs; specialize hδ S v xs
      simp_all
    rw [← stdModel.prf_iff_models cons (subst IsSigma.Pf ![(Code.Formula δ).1]) (Pf_isSigma δ),
        ← prf_iff_prf_Pf_code cons δ] at models
    apply h2
    exact stdModel.sound cons δ models

end HF
