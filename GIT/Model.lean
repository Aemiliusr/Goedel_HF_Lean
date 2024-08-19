import GIT.Basic

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

abbrev C := Lang.Term Empty

namespace C

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
