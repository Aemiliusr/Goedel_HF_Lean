import GIT.Model

open FirstOrder Language

suppress_compilation

namespace HF

inductive IsInSSigma : Lang.BoundedFormula α n → Prop where
| atomic_mem : IsInSSigma (.var i ∈' .var j)
| disj (h1 : IsInSSigma φ) (h2 : IsInSSigma ψ) : IsInSSigma (φ ⊔ ψ)
| conj (h1 : IsInSSigma φ) (h2 : IsInSSigma ψ) : IsInSSigma (φ ⊓ ψ)
| ex {φ : Lang.BoundedFormula α (n+1)} (h : IsInSSigma φ) : IsInSSigma (∃' φ)
| all {φ : Lang.BoundedFormula α (n+1)} (h : IsInSSigma φ) :
    IsInSSigma (∀' ((&n ∈' .var i) ⟹ φ))

abbrev IsSigma (φ : Lang.BoundedFormula α n) : Prop :=
  ∃ (ψ : Lang.BoundedFormula α n), IsInSSigma ψ ∧ prf {} (φ ⇔ ψ)

lemma subset_isSigma :
    IsSigma (∀' ((&0 ∈' .var (.inl 0)) ⟹ (&0 ∈' .var (.inl 1))) : Lang.Formula (Fin 2)) := by
  use ∀' ((&0 ∈' .var (.inl 0)) ⟹ (&0 ∈' .var (.inl 1)))
  refine ⟨?_, by rw [completeness]; intros _ _ _; simp ⟩
  apply IsInSSigma.all
  apply IsInSSigma.atomic_mem


end HF
