import GIT.Coding

/-!
# Σ-formulas

In this file, Section 2 of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness
Theorems' is formalised. It systematically presents the theory on Σ-formulas.

## Main definitions
* `HF.IsInSSigma` : The (strict) Σ family of first-order formulas.
* `HF.IsSigma` : A first-order formula is a Σ-formula if it is equivalent to a formula in
  (strict) Σ.

## Main statements
* `HF.stdModel.prf_iff_models` : Every Σ-sentence is a theorem of HF iff it is modeled by the
  standard model of HF, if HF is consistent.

## References
* S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
  mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.

## TO DO
* Formalise missing lemmas.
* Define Σ◁-formulas.
* Complete the proof of `HF.stdModel.prf_iff_models`.
-/

open FirstOrder Language

suppress_compilation

namespace HF

/-- The (strict) Σ family of first-order formulas. -/
inductive IsInSSigma : Lang.BoundedFormula α n → Prop where
| atomic_mem : IsInSSigma (.var i ∈' .var j)
| disj (h1 : IsInSSigma φ) (h2 : IsInSSigma ψ) : IsInSSigma (φ ⊔ ψ)
| conj (h1 : IsInSSigma φ) (h2 : IsInSSigma ψ) : IsInSSigma (φ ⊓ ψ)
| ex {φ : Lang.BoundedFormula α (n+1)} (h : IsInSSigma φ) : IsInSSigma (∃' φ)
| all {φ : Lang.BoundedFormula α (n+1)} (h : IsInSSigma φ) :
    IsInSSigma (∀' ((&n ∈' .var i) ⟹ φ))

/-- A first-order formula is a Σ-formula if it is equivalent to a formula in (strict) Σ. -/
abbrev IsSigma (φ : Lang.BoundedFormula α n) : Prop :=
  ∃ (ψ : Lang.BoundedFormula α n), IsInSSigma ψ ∧ ⊢ (φ ⇔ ψ)

lemma subset_isSigma :
    IsSigma (∀' ((&2 ∈' &0) ⟹ (&2 ∈' &1)) : Lang.BoundedFormula Empty 2) := by
  use (∀' ((&2 ∈' &0) ⟹ (&2 ∈' &1)))
  refine ⟨?_, by rw [completeness]; intros _ _ _ _; simp⟩
  exact IsInSSigma.all IsInSSigma.atomic_mem

lemma eq_isSigma :
    IsSigma ((&0 =' &1) : Lang.BoundedFormula Empty 2) := by
  use (∀' ((&2 ∈' &0) ⟹ (&2 ∈' &1))) ⊓ (∀' ((&2 ∈' &1) ⟹ (&2 ∈' &0)))
  constructor
  · apply IsInSSigma.conj
    · exact IsInSSigma.all IsInSSigma.atomic_mem
    · exact IsInSSigma.all IsInSSigma.atomic_mem
  · rw [completeness]
    intros _ _ _ _
    simp only [Fin.isValue, Function.comp_apply, Nat.reduceAdd, BoundedFormula.realize_iff,
      BoundedFormula.realize_bdEqual, Term.realize_var, Sum.elim_inr, HFSet.exten_prop,
      BoundedFormula.realize_inf, BoundedFormula.realize_all, Nat.succ_eq_add_one,
      BoundedFormula.realize_imp, BoundedFormula.realize_rel, mem_rel, Matrix.cons_val_zero,
      Fin.snoc, Fin.val_two, lt_self_iff_false, ↓reduceDIte, cast_eq, Matrix.cons_val_one,
      Matrix.head_cons, Fin.val_zero, Nat.ofNat_pos, Fin.castLT, Fin.zero_eta, Fin.castSucc_zero,
      Fin.val_one, Nat.one_lt_ofNat, Fin.mk_one, Fin.castSucc_one]
    aesop

lemma enlarge_isSigma : IsSigma (&0 =' .func ◁' ![&1, &2] : Lang.BoundedFormula Empty 3) := sorry

lemma eq_empty_isSigma : IsSigma (&0 =' .func ∅' Fin.elim0 : Lang.BoundedFormula Empty 1) := sorry

lemma mem_empty_isSigma : IsSigma (&0 ∈' .func ∅' Fin.elim0 : Lang.BoundedFormula Empty 1) := sorry

lemma empty_mem_isSigma : IsSigma (.func ∅' Fin.elim0 ∈' &0 : Lang.BoundedFormula Empty 1) := sorry

namespace stdModel

/-- Every Σ-sentence is a theorem of HF iff it is modeled by the standard model of HF,
if HF is consistent. -/
theorem prf_iff_models (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ))
    (α : Lang.Sentence) (h : IsSigma α)  : ⊢ α ↔ stdModel ⊧ α := by
  refine ⟨sound cons α, ?_⟩
  sorry

end stdModel

end HF
