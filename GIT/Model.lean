import GIT.Basic

open FirstOrder Language BoundedFormula

local notation "∅'" => HF.Lang.emptySetSymbol

local notation " ◁' " => HF.Lang.enlargementSymbol

local notation t " ∈' " s => HF.Lang.membershipSymbol.boundedFormula ![t, s]

universe u

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

--completeness gives weird error about universes
lemma symm (σ τ : C) : Equiv σ τ → Equiv τ σ := by
  unfold Equiv; simp only
  intro h
  sorry
  -- rw [← completeness] at *
  -- intros s inst1 inst2; specialize h s
  -- intro c; specialize h c
  -- simp_all [Formula.Realize]

--completeness gives weird error about universes
lemma trans (σ τ ν : C) : Equiv σ τ → Equiv τ ν → Equiv σ ν := by
  unfold Equiv; simp only
  intros h1 h2
  sorry
  -- rw [← completeness] at *
  -- intros s inst1 inst2; specialize h1 s; specialize h2 s
  -- intro c; specialize h1 c; specialize h2 c
  -- simp_all [Formula.Realize]

end Equiv

instance setoid : Setoid C :=
  ⟨Equiv,
    ⟨Equiv.refl, (by intro σ τ; exact Equiv.symm σ τ), (by intro σ τ ν; exact Equiv.trans σ τ ν)⟩⟩

end C

def term_model : Type := Quotient C.setoid

instance : Lang.Structure term_model where
  funMap {n} _ h := match n with
  | 0 => Quotient.mk C.setoid (.func ∅' Fin.elim0)
  | 2 => Quotient.mk C.setoid (.func ◁' ![(h 0).out, (h 1).out])
  RelMap {n} _ h := match n with
  | 2 => ⊢ (((h 0).out).relabel .inl) ∈' (((h 1).out).relabel .inl)

instance (consistent : ¬∃ (φ : Lang.Formula α), ⊢ φ ∧ ⊢ ∼φ) :
    HF.Model term_model := by sorry

end HF
