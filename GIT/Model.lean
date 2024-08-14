import GIT.Basic

open FirstOrder Language BoundedFormula

local notation "∅'" => HF.Lang.emptySetSymbol

local notation " ◁' " => HF.Lang.enlargementSymbol

local notation t " ∈' " s => HF.Lang.membershipSymbol.boundedFormula ![t, s]

universe u

namespace HF

inductive C : Type u :=
| zero : C
| cons : C → C → C

inductive Const : Lang.Term Empty → Prop
| empty : Const (.func ∅' Fin.elim0)
| enlarge (σ τ : Lang.Term Empty) (h1 : Const σ) (h2 : Const τ) : Const (.func ◁' ![σ, τ])

namespace C

def Equiv : Lang.Term (Fin 0 ⊕ Fin 0) → Lang.Term (Fin 0 ⊕ Fin 0) → Prop
  | σ, τ => ⊢ σ =' τ

-- need reflexivity, symmetry, and transitivity
instance setoid : Setoid (Lang.Term (Fin 0 ⊕ Fin 0)) :=
  ⟨C.Equiv, sorry⟩

end C

def HFSet : Type := Quotient C.setoid

end HF
