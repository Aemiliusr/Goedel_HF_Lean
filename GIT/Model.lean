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
  apply prf.Eq
  simp only [Equality.Theory, Set.iUnion_singleton_eq_range, Set.mem_union, Set.mem_range,
    Set.mem_iUnion]
  left; left; left
  use σ
  rfl

lemma symm (σ τ : C) : Equiv σ τ → Equiv τ σ := by
  unfold Equiv; simp only
  intro h
  rw [completeness] at *
  intros s inst1 c; specialize h s c
  simp_all [Formula.Realize]

lemma trans (σ τ ν : C) : Equiv σ τ → Equiv τ ν → Equiv σ ν := by
  unfold Equiv; simp only
  intros h1 h2
  rw [completeness] at *
  intros s inst1 c; specialize h1 s c; specialize h2 s c
  simp_all [Formula.Realize]

end Equiv

instance setoid : Setoid C :=
  ⟨Equiv,
    ⟨Equiv.refl, (by intro σ τ; exact Equiv.symm σ τ), (by intro σ τ ν; exact Equiv.trans σ τ ν)⟩⟩

end C

def term_model : Type := Quotient C.setoid

namespace term_model

instance : Lang.Structure term_model where
  funMap {n} _ h := match n with
  | 0 => Quotient.mk C.setoid (.func ∅' Fin.elim0)
  | 2 => Quotient.mk C.setoid (.func ◁' ![(h 0).out, (h 1).out])
  RelMap {n} _ h := match n with
  | 2 => ⊢ (((h 0).out).relabel .inl) ∈' (((h 1).out).relabel .inl)

lemma ax1_aux (cons : ¬(⊢ (⊥ : Lang.Formula α))) (t : Lang.Term α') :
    term_model ⊧ Axiom1 t := by sorry

lemma ax2_aux (t1 t2 t3 : Lang.Term α) : term_model ⊧ Axiom2 t1 t2 t3 := by sorry

lemma ax3_aux (ψ : Lang.BoundedFormula α 1) : term_model ⊧ Axiom3 ψ := by sorry

instance (cons : ¬(⊢ (⊥ : Lang.Formula α))) : Model term_model where
  struc := inferInstance
  realize_of_mem := by
    intros α φ ax
    rcases ax with ⟨ax1 | ax2⟩ | ax3
    · simp only [Set.iUnion_singleton_eq_range, Set.mem_range] at ax1
      rcases ax1 with ⟨t, ax1⟩
      rw [← ax1]
      exact ax1_aux cons t
    · simp only [Set.iUnion_singleton_eq_range, Set.mem_iUnion, Set.mem_range] at ax2
      rcases ax2 with ⟨t1, ⟨t2, ⟨t3, ax2⟩⟩⟩
      rw [← ax2]
      exact ax2_aux t1 t2 t3
    · simp only [Set.iUnion_singleton_eq_range, Set.mem_range] at ax3
      rcases ax3 with ⟨ψ, ax3⟩
      rw [← ax3]
      exact ax3_aux ψ

end term_model

end HF
