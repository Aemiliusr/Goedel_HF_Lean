import GIT.Basic

open FirstOrder Language BoundedFormula Classical

suppress_compilation

namespace HF

abbrev C := Lang.Term Empty

namespace C

@[elab_as_elim]
def rec {motive : C → Type} (h0 : motive (.func ∅' Fin.elim0))
  (h2 : ∀ {σ} {τ}, motive σ → motive τ → motive (.func ◁' ![σ, τ])) : ∀ σ, motive σ
| .var x => by cases x
| @Term.func _ _ 0 f ts => by convert h0
| @Term.func _ _ 2 f ts => by
    convert h2 (rec h0 h2 (ts 0)) (rec h0 h2 (ts 1))
    ext i
    fin_cases i <;> rfl

@[elab_as_elim]
theorem ind {motive : C → Prop} (h0 : motive (.func ∅' Fin.elim0))
  (h2 : ∀ {σ} {τ}, motive σ → motive τ → motive (.func ◁' ![σ, τ])) : ∀ σ, motive σ
| .var x => by cases x
| @Term.func _ _ 0 f ts => by convert h0
| @Term.func _ _ 2 f ts => by
    convert h2 (ind h0 h2 (ts 0)) (ind h0 h2 (ts 1))
    ext i
    fin_cases i <;> rfl

def length : C → ℕ := rec (0) (fun lσ lτ ↦ lσ + lτ + 1)

lemma length_empty : length (.func ∅' Fin.elim0) = 0 := rfl

lemma length_enlarge {σ τ} : length (.func ◁' ![σ, τ]) = length σ + length τ + 1 := rfl

lemma exists_finset_shorter_and_mem_iff_iSup (τ : C) (ne_emp : τ ≠ .func ∅' Fin.elim0) :
    ∃ (F : Finset C), (∃ ν, ν ∈ F) ∧ (∀ ν ∈ F, length ν < length τ) ∧
    ⊢ ∀' ((&0 ∈' τ.relabel .inl) ⇔ iSup F (fun ν => (&0 =' ν.relabel .inl))) := by
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

lemma exists_mem_and_notin_of_not_eq (σ τ : C) (h : ¬ ⊢ (σ.relabel .inl =' τ.relabel .inl)) :
    ∃ (ν : C), (⊢ (ν.relabel .inl ∈' σ.relabel .inl ) ∧ ⊢ ∼(ν.relabel .inl ∈' τ.relabel .inl ))
    ∨ (⊢ ∼(ν.relabel .inl ∈' σ.relabel .inl ) ∧ ⊢ (ν.relabel .inl ∈' τ.relabel .inl )) := by
  sorry

lemma ne_of_not_eq (σ τ : C) (h : ¬ ⊢ (σ.relabel .inl =' τ.relabel .inl)) :
    ⊢ ∼(σ.relabel .inl =' τ.relabel .inl) := by
  apply exists_mem_and_notin_of_not_eq at h
  rcases h with ⟨ν, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  <;> rw [completeness] at *
  <;> intros S inst v
  <;> specialize h1 S v <;> specialize h2 S v
  <;> simp only [Formula.Realize, realize_rel, mem_rel, Fin.isValue, Matrix.cons_val_zero,
    Term.realize_relabel, Sum.elim_comp_inl, Matrix.cons_val_one, Matrix.head_cons, realize_not,
    realize_bdEqual] at *
  <;> rw [HFSet.exten_prop] <;> push_neg
  <;> use Term.realize v ν
  <;> simp_all

lemma eq_of_forall_mem_iff_mem (σ τ : C) (cons : ¬ ∃ (φ : Lang.Sentence), ⊢ φ ∧ ⊢ ∼φ)
    (h : ∀ (ν : C), ⊢ (ν.relabel .inl ∈' σ.relabel .inl) ↔ ⊢ (ν.relabel .inl ∈' τ.relabel .inl)) :
    ⊢ σ.relabel .inl =' τ.relabel .inl := by
  by_contra contra
  apply exists_mem_and_notin_of_not_eq at contra
  rcases contra with ⟨μ, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> specialize h μ
  · rw [h] at h1
    apply cons
    use (μ.relabel .inl ∈' τ.relabel .inl)
  · rw [← h] at h2
    apply cons
    use (μ.relabel .inl ∈' σ.relabel .inl)

def Equiv : C → C → Prop
  | σ, τ => ⊢ σ.relabel .inl =' τ.relabel .inl

namespace Equiv

lemma refl (σ : C) : Equiv σ σ := by
  unfold Equiv; simp only
  rw [completeness]
  intros s inst1 v
  simp_all [Formula.Realize]

lemma symm (σ τ : C) : Equiv σ τ → Equiv τ σ := by
  unfold Equiv; simp only
  intro h
  rw [completeness] at *
  intros s inst1 v; specialize h s v
  simp_all [Formula.Realize]

lemma trans (σ τ ν : C) : Equiv σ τ → Equiv τ ν → Equiv σ ν := by
  unfold Equiv; simp only
  intros h1 h2
  rw [completeness] at *
  intros s inst1 v; specialize h1 s v; specialize h2 s v
  simp_all [Formula.Realize]

end Equiv

instance setoid : Setoid C :=
  ⟨Equiv,
    ⟨Equiv.refl, (by intro σ τ; exact Equiv.symm σ τ), (by intro σ τ ν; exact Equiv.trans σ τ ν)⟩⟩

end C

def stdModel : Type := Quotient C.setoid

namespace stdModel

instance : Lang.Structure stdModel where
  funMap {n} _ h := match n with
  | 0 => Quotient.mk C.setoid (.func ∅' Fin.elim0)
  | 2 => Quotient.mk C.setoid (.func ◁' ![(h 0).out, (h 1).out])
  RelMap {n} _ h := match n with
  | 2 => ⊢ (((h 0).out).relabel .inl) ∈' (((h 1).out).relabel .inl)

lemma ax1_aux (cons : ¬(⊢ (⊥ : Lang.Formula α))) : models (α := α) stdModel Axiom1 := by sorry

lemma ax2_aux : models (α := α) stdModel Axiom2 := by sorry

lemma ax3_aux (ψ : Lang.BoundedFormula α 1) : stdModel ⊧ Axiom3 ψ := by sorry

instance model_of_consistent (cons : ∀ α, ¬(⊢ (⊥ : Lang.Formula α))) : Model stdModel where
  struc := inferInstance
  realize_of_mem := by
    intros α φ ax
    rcases ax with ⟨ax1 | ax2⟩ | ax3
    · rw [ax1]
      apply ax1_aux
      exact cons α
    · rw [ax2]
      exact ax2_aux
    · simp only [Set.iUnion_singleton_eq_range, Set.mem_range] at ax3
      rcases ax3 with ⟨ψ, ax3⟩
      rw [← ax3]
      exact ax3_aux ψ

end stdModel

end HF
