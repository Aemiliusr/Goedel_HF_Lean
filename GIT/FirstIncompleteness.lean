import GIT.Pf

/-!
# Gödel's first incompleteness theorem

In this file, Sections 5 and 6  of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness
Theorems' are formalised. It finalises the proof of the first incompleteness theorem.

## Main statements
* `HF.diagonal` : Gödel's diagonal lemma.
* `HF.first_incompleteness` : Gödel's first incompleteness theorem.

## Implementation notes
* In `HF.Code.exists_pFunc_forall_form_eq_code_form`, the existence of a p-function is stated as
  the existence of the corresponding functional.

## References
* S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
  mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.

## TO DO
* Formalise recursion on rank, i.e. Appendix 4 of S. Swierczkowski: 'Finite Sets and Gödel’s
  Incompleteness Theorems'.
* Formalise the replacement function, i.e. Section 5 of S. Swierczkowski: 'Finite Sets and Gödel’s
  Incompleteness Theorems'.
* Formalise the auxiliary lemmas of Gödel's diagonal lemma, i.e. prove
  `HF.Code.exists_pFunc_forall_form_eq_code_form`.
* Prove `HF.diagonal`.
-/

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

namespace Code

lemma exists_pFunc_forall_form_eq_code_form :
    ∃ (ψ : Lang.BoundedFormula (Fin 1) 1), ∀ (φ : Lang.Formula (Fin 1)),
    ⊢ (∃' ((&0 =' ((Code.Formula (subst φ ![(Code.Formula φ).1])).1).relabel .inl) ⊓
    subst ψ ![(Code.Formula φ).1]) : Lang.Sentence) := sorry

end Code

/-- Gödel's diagonal lemma. -/
theorem diagonal (α : Lang.Formula (Fin 1)) : ∃ (δ : Lang.Sentence),
    ⊢ δ ⇔ (subst α ![(Code.Formula δ).1]) := sorry

/-- Gödel's first incompleteness theorem. -/
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
