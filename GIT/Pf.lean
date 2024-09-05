import GIT.Sigma

/-!
# The provability formula Pf

In this file, Section 3 and a part of Section 4  of S. Swierczkowski: 'Finite Sets and Gödel’s
Incompleteness Theorems' are formalised. It constructs the provability formula Pf.

## Main definitions
* `HF.IsSigma.Pf` : The Σ-formula Pf, i.e. the provability formula.

## Main statements
* `HF.prf_iff_prf_Pf_code` : Every first-order formula φ is a theorem of HF iff Pf with the code of
  φ substituted is a theorem of HF, if HF is consistent.

## References
* S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
  mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.

## TO DO
* Formalise the main body of constructing the formula Pf.
* Prove `HF.Pf_isSigma`.
* Prove `HF.prf_iff_prf_Pf_code`.
-/

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

namespace IsSigma

/-- The Σ-formula Pf, i.e. the provability formula. -/
abbrev Pf : Lang.Formula (Fin 1) := sorry

end IsSigma

lemma Pf_isSigma [Fintype α] (φ : Lang.BoundedFormula α n) :
    IsSigma (subst IsSigma.Pf ![(Code.Formula φ).1]) := sorry

/-- Every first-order formula φ is a theorem of HF iff Pf with the code of φ substituted is a
theorem of HF, if HF is consistent. -/
theorem prf_iff_prf_Pf_code (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) [Fintype α]
    (φ : Lang.BoundedFormula α n) : ⊢ φ ↔ ⊢ (subst IsSigma.Pf ![(Code.Formula φ).1]) := sorry

end HF
