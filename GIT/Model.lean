import GIT.Basic

/-!
# The standard model of HF

In this file, the sixth appendix of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness
Theorems' is formalised. It systematically presents results on constant terms and the standard
model of HF.

## Main definitions
* `HF.C` : The type of constant terms.
* `HF.C.length` : The length of a constant term, i.e. the number of occurrences of `◁`.
* `HF.C.Equiv` : Equivalence relation on constant terms.
* `HF.stdModel` : The standard model of HF.

## Main statements
* `HF.C.setoid` : `≈` is an equivalence relation on constant terms.
* `HF.stdModel.struc` : The standard model of HF is a first-order structure.
* `HF.stdModel.model_of_consistent` : The standard model of HF is a model of HF, if HF is
  consistent.

## Notations
* `≈` : Equivalence relation on constant terms, see `HF.C.Equiv`.

## References
* S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
  mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.

## TO DO
* Prove `HF.C.exists_mem_and_notin_of_not_eq`.
* Complete the proof of `HF.stdModel.model_of_consistent`.
* Fix the errors in `HF.stdModel.sound` and `HF.stdModel.models_iff_of_prf_iff`.
-/

open FirstOrder Language BoundedFormula Classical

suppress_compilation

namespace HF

/-- The type of constant terms. -/
abbrev C := Lang.Term Empty

namespace C

/-- Recursion on length of constant terms. -/
@[elab_as_elim]
def rec {motive : C → Type} (h0 : motive (.func ∅' Fin.elim0))
  (h2 : ∀ {σ} {τ}, motive σ → motive τ → motive (.func ◁' ![σ, τ])) : ∀ σ, motive σ
| .var x => by cases x
| @Term.func _ _ 0 f ts => by convert h0
| @Term.func _ _ 2 f ts => by
    convert h2 (rec h0 h2 (ts 0)) (rec h0 h2 (ts 1))
    ext i
    fin_cases i <;> rfl

/-- Induction on length of constant terms. -/
@[elab_as_elim]
lemma ind {motive : C → Prop} (h0 : motive (.func ∅' Fin.elim0))
  (h2 : ∀ {σ} {τ}, motive σ → motive τ → motive (.func ◁' ![σ, τ])) : ∀ σ, motive σ
| .var x => by cases x
| @Term.func _ _ 0 f ts => by convert h0
| @Term.func _ _ 2 f ts => by
    convert h2 (ind h0 h2 (ts 0)) (ind h0 h2 (ts 1))
    ext i
    fin_cases i <;> rfl

lemma exist_terms_enlarge_of_ne_empty (σ : C) (h : σ ≠ .func ∅' Fin.elim0) :
    ∃ τ μ, σ = .func ◁' ![τ, μ] := by
  induction σ using C.ind with
  | h0 => exfalso; exact h rfl
  | h2 _hσ _hτ =>
    rename_i σ τ
    use σ; use τ

lemma realize_eq_of_eq (σ τ : C) (S : Type) [Model S] (v : Empty → S)
    (h : ⊢ ((σ.relabel .inl =' τ.relabel .inl) : Lang.Sentence)) :
    Term.realize v σ = Term.realize v τ := by
  rw [completeness] at h
  specialize h S v
  simp [Formula.Realize] at h
  exact h

/-- The length of a constant term, i.e. the number of occurrences of `◁`. -/
def length : C → ℕ := rec (0) (fun lσ lτ ↦ lσ + lτ + 1)

lemma length_empty : length (.func ∅' Fin.elim0) = 0 := rfl

lemma length_enlarge {σ τ} : length (.func ◁' ![σ, τ]) = length σ + length τ + 1 := rfl

lemma exists_finset_shorter_and_mem_iff_iSup (τ : C) (ne_emp : τ ≠ .func ∅' Fin.elim0) :
    ∃ (F : Finset C), (∃ ν, ν ∈ F) ∧ (∀ ν ∈ F, length ν < length τ) ∧
    ⊢ (∀' ((&0 ∈' τ.relabel .inl) ⇔ iSup F (fun ν => (&0 =' ν.relabel .inl))) : Lang.Sentence) := by
    induction τ using ind with
    | h0 => exfalso; exact ne_emp rfl
    | h2 hσ _hμ =>
      rename_i σ μ
      by_cases σ_eq_emp : σ = .func ∅' Fin.elim0
      · refine ⟨{μ}, ⟨by simp, ⟨?_, ?_⟩⟩⟩
        · simp [length_enlarge]
          linarith
        · rw [σ_eq_emp, completeness]
          intros _ _ _
          simp [Formula.Realize]
      · apply hσ at σ_eq_emp
        rcases σ_eq_emp with ⟨F, ⟨_, ⟨hF₂, hF₃⟩⟩⟩
        refine ⟨insert μ F, ⟨by simp, ⟨?_, ?_⟩⟩⟩
        · simp [length_enlarge]
          refine ⟨by linarith, ?_⟩
          intro ν hν; specialize hF₂ ν hν
          linarith
        · rw [completeness] at *
          intros S inst v; specialize hF₃ S v
          simp [Formula.Realize, Fin.snoc] at *
          intro x; specialize hF₃ x
          rw [hF₃]
          exact Iff.symm Or.comm

lemma exists_mem_and_notin_of_not_eq (σ τ : C)
    (h : ¬ ⊢ ((σ.relabel .inl =' τ.relabel .inl) : Lang.Sentence)) :
    ∃ (ν : C), (⊢ (ν.relabel .inl ∈' σ.relabel .inl : Lang.Sentence) ∧
    ⊢ (∼(ν.relabel .inl ∈' τ.relabel .inl) : Lang.Sentence))
    ∨ (⊢ (∼(ν.relabel .inl ∈' σ.relabel .inl) : Lang.Sentence) ∧
    ⊢ (ν.relabel .inl ∈' τ.relabel .inl : Lang.Sentence)) := by
  sorry

lemma ne_of_not_eq (σ τ : C) (h : ¬ ⊢ (σ.relabel .inl =' τ.relabel .inl : Lang.Sentence)) :
    ⊢ (∼(σ.relabel .inl =' τ.relabel .inl) : Lang.Sentence) := by
  apply exists_mem_and_notin_of_not_eq at h
  rcases h with ⟨ν, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  <;> rw [completeness] at *
  <;> intros S inst v xs
  <;> specialize h1 S v xs <;> specialize h2 S v xs
  <;> simp only [Formula.Realize, realize_rel, mem_rel, Fin.isValue, Matrix.cons_val_zero,
    Term.realize_relabel, Sum.elim_comp_inl, Matrix.cons_val_one, Matrix.head_cons, realize_not,
    realize_bdEqual] at *
  <;> rw [HFSet.exten_prop] <;> push_neg
  <;> use Term.realize v ν
  <;> simp_all

lemma eq_of_forall_mem_iff_mem (σ τ : C) (cons : ¬ ∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)
    (h : ∀ (ν : C), ⊢ (ν.relabel .inl ∈' σ.relabel .inl : Lang.Sentence) ↔
    ⊢ (ν.relabel .inl ∈' τ.relabel .inl : Lang.Sentence)) :
    ⊢ (σ.relabel .inl =' τ.relabel .inl : Lang.Sentence) := by
  by_contra contra
  apply exists_mem_and_notin_of_not_eq at contra
  rcases contra with ⟨μ, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> specialize h μ
  · rw [h] at h1
    apply cons
    use (μ.relabel .inl ∈' τ.relabel .inl)
  · rw [← h] at h2
    apply cons
    use (μ.relabel .inl ∈' σ.relabel .inl)

/-- Equivalence relation on constant terms. -/
def Equiv : C → C → Prop
  | σ, τ => ⊢ (σ.relabel .inl =' τ.relabel .inl : Lang.Sentence)

instance : HasEquiv C := ⟨Equiv⟩

namespace Equiv

@[simp] lemma equiv_iff (σ τ : C) : σ ≈ τ ↔ ⊢ (σ.relabel .inl =' τ.relabel .inl : Lang.Sentence) :=
  Iff.rfl

lemma refl (σ : C) : σ ≈ σ := by
  simp only [equiv_iff]
  rw [completeness]
  intros s inst1 v
  simp_all [Formula.Realize]

lemma symm (σ τ : C) : σ ≈ τ → τ ≈ σ := by
  simp only [equiv_iff]
  intro h
  rw [completeness] at *
  intros s inst1 v; specialize h s v
  simp_all [Formula.Realize]

lemma trans (σ τ ν : C) : σ ≈ τ → τ ≈ ν → σ ≈ ν := by
  simp only [equiv_iff]
  intros h1 h2
  rw [completeness] at *
  intros s inst1 v; specialize h1 s v; specialize h2 s v
  simp_all [Formula.Realize]

end Equiv

/-- `≈` is an equivalence relation on constant terms. -/
instance setoid : Setoid C :=
  ⟨Equiv,
    ⟨Equiv.refl, (by intro σ τ; exact Equiv.symm σ τ), (by intro σ τ ν; exact Equiv.trans σ τ ν)⟩⟩

end C

open C Equiv

/-- The standard model of HF. -/
abbrev stdModel : Type := Quotient setoid

namespace stdModel

/-- The standard model of HF is a first-order structure. -/
instance struc : Lang.Structure stdModel where
  funMap {n} _ h := match n with
  | 0 => Quotient.mk setoid (.func ∅' Fin.elim0)
  | 2 => Quotient.mk setoid (.func ◁' ![(h 0).out, (h 1).out])
  RelMap {n} _ h := match n with
  | 2 => ⊢ ((((h 0).out).relabel .inl) ∈' (((h 1).out).relabel .inl) : Lang.Sentence)

lemma mem_iff (σ τ : stdModel) : σ ∈ τ ↔
    ⊢ (((σ.out).relabel .inl) ∈' ((τ.out).relabel .inl) : Lang.Sentence) :=
  Eq.to_iff rfl

lemma empty_iff_of_consistent_aux (σ τ : C) (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ))
    (h : ⊢ ((@Term.relabel Lang Empty (Empty ⊕ Fin 0) Sum.inl (func ◁' ![σ, τ])) ='
    (@Term.relabel Lang Empty (Empty ⊕ Fin 0) Sum.inl (func ∅' Fin.elim0)))) : False := by
  have : ⊢ (∼(∃' ((&0 ∈' σ.relabel .inl) ⊔ (&0 =' τ.relabel .inl))) : Lang.Sentence) := by
    simp only [completeness] at *
    intros S inst v xs; specialize h S v xs
    simp only [not_exists, not_and, not_forall, Formula.Realize, realize_not, Decidable.not_not,
      realize_bdEqual, Term.realize_func, enlarge_fun, Fin.isValue, Matrix.cons_val_zero,
      Term.realize_relabel, Sum.elim_comp_inl, Matrix.cons_val_one, Matrix.head_cons, empty_fun,
      Nat.reduceAdd, Function.comp_apply, realize_ex, Nat.succ_eq_add_one, realize_sup, realize_rel,
      mem_rel, Term.realize_var, Sum.elim_inr, Fin.snoc, Fin.coe_fin_one, lt_self_iff_false,
      ↓reduceDIte, cast_eq, exists_or_eq_right, not_true_eq_false] at *
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      enlarge_fun, HFSet.exten_prop, HFSet.mem_enlarge, HFSet.in_empty_iff_false, iff_false, not_or,
      not_forall] at h
    specialize h (Term.realize v τ)
    rcases h with ⟨_, ⟨x, h2⟩⟩; apply h2
    simp [HFSet.exten_prop]
  apply cons
  use (∃' ((&0 ∈' σ.relabel .inl) ⊔ (&0 =' τ.relabel .inl)))
  refine ⟨?_, this⟩
  rw [completeness]
  intros S inst v
  simp [Formula.Realize, Fin.snoc]

lemma empty_iff_of_consistent (σ : stdModel) (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) :
    σ = ∅ ↔ σ.out = .func ∅' Fin.elim0 := by
  constructor
  · rintro rfl
    have := Quotient.mk_out (func ∅' Fin.elim0 : C)
    rw [equiv_iff] at this
    by_contra contra
    apply exist_terms_enlarge_of_ne_empty at contra
    rcases contra with ⟨σ, ⟨τ, hσ⟩⟩
    have h : ⟦func ∅' Fin.elim0⟧.out = (∅ : stdModel).out := rfl
    rw [h, hσ] at this
    exact empty_iff_of_consistent_aux σ τ cons this
  · intro h
    apply congrArg (Quotient.mk setoid) at h
    aesop

lemma empty_out_relabel_eq_of_consistent (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) :
    (((∅ : stdModel).out).relabel .inl) = (.func ∅' Fin.elim0 : Lang.Term (Empty ⊕ Fin 0))  := by
  have : (∅ : stdModel).out = (.func ∅' Fin.elim0 : C) := by rw [← empty_iff_of_consistent ∅ cons]
  rw [this]
  simp only [Term.relabel, Term.func.injEq, heq_eq_eq, true_and]
  ext i
  fin_cases i

lemma ax1_aux_aux (ν μ : C) :
    (Quotient.mk C.setoid ν) ∈ (Quotient.mk C.setoid (func ◁' ![μ, ν])) := by
  rw [mem_iff, completeness]
  intros S inst v
  simp only [Formula.Realize, realize_rel, mem_rel, Fin.isValue, Matrix.cons_val_zero,
    Term.realize_relabel, Sum.elim_comp_inl, Matrix.cons_val_one, Matrix.head_cons]
  rw [C.realize_eq_of_eq (Quotient.mk C.setoid ν).out ν S v
    (by rw [← equiv_iff]; exact Quotient.mk_out ν)]
  rw [C.realize_eq_of_eq (Quotient.mk C.setoid (func ◁' ![μ, ν])).out (func ◁' ![μ, ν]) S v
    (by rw [← equiv_iff]; exact Quotient.mk_out (func ◁' ![μ, ν]) )]
  simp

lemma ax1_aux (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) :
    stdModel ⊧ Axiom1 := by
  unfold models Axiom1
  simp [Formula.Realize, Fin.snoc]
  intro σ
  constructor
  · rintro rfl
    intros τ h
    rw [mem_iff, empty_out_relabel_eq_of_consistent cons] at h
    have : ⊢ (∼(((τ.out).relabel .inl) ∈' .func ∅' Fin.elim0) : Lang.Sentence) :=
      by rw [completeness]; intros _ _ _; simp [Formula.Realize]
    apply cons
    use (((τ.out).relabel .inl) ∈' .func ∅' Fin.elim0)
  · intro h
    rw [empty_iff_of_consistent σ cons]
    by_contra contra
    apply C.exist_terms_enlarge_of_ne_empty at contra
    rcases contra with ⟨μ, ⟨ν, hσ⟩⟩
    apply congrArg (Quotient.mk C.setoid) at hσ
    simp only [Quotient.out_eq] at hσ
    subst σ
    apply h (Quotient.mk C.setoid ν) (ax1_aux_aux ν μ)

lemma ax2_aux : stdModel ⊧ Axiom2 := by sorry

lemma ax3_aux (ψ : Lang.BoundedFormula α 1) : stdModel ⊧ Axiom3 ψ := by sorry

/-- The standard model of HF is a model of HF, if HF is consistent. -/
instance model_of_consistent (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) :
    Model stdModel where
  non_empty := by use ∅
  struc := inferInstance
  realize_of_mem_theory := by
    intros φ ax v xs
    rcases ax with ax1 | ax2
    · rw [ax1]
      apply ax1_aux
      exact cons
    · rw [ax2]
      apply ax2_aux
  realize_of_mem_scheme := by
    intros α φ ax v xs
    simp only [Scheme, Set.iUnion_singleton_eq_range, Set.mem_range] at ax
    rcases ax with ⟨ψ, ax⟩
    rw [← ax]
    apply ax3_aux

lemma sound (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)) (φ : Lang.Sentence) (h : ⊢ φ) :
    stdModel ⊧ φ := by
  have := model_of_consistent cons
  rw [completeness] at h
  specialize h stdModel
  -- exact h
  -- weird error
  sorry

lemma models_iff_of_prf_iff (cons : ¬(∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ))
    (φ ψ : Lang.BoundedFormula α n) (h : ⊢ φ ⇔ ψ) :
    stdModel ⊧ φ ↔ stdModel ⊧ ψ := by
  have := model_of_consistent cons
  -- exact HF.models_iff_of_prf_iff stdModel φ ψ h
  -- weird error
  sorry

end stdModel

end HF
