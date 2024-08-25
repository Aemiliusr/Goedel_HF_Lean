import GIT.Model

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

abbrev pair (σ τ : C) : C :=
  .func ◁' ![(.func ◁' ![.func ∅' Fin.elim0, .func ◁' ![.func ∅' Fin.elim0, σ] ]),
  .func ◁' ![.func ◁' ![.func ∅' Fin.elim0, σ] ,τ] ]

inductive IsInΓ0 : C → Prop where
| empty : IsInΓ0 (.func ∅' Fin.elim0)
| enlarge (hσ : IsInΓ0 σ) : IsInΓ0 (.func ◁' ![σ, σ])

inductive IsInΓ : C → Prop where
| isInΓ0 (h : IsInΓ0 σ) : IsInΓ σ
| pair (hσ : IsInΓ σ) (hτ : IsInΓ τ) : IsInΓ (pair σ τ)

lemma ne_of_isInΓ_and_distinct (σ τ : C) (hσ : IsInΓ σ) (hτ : IsInΓ τ) (h : σ ≠ τ) :
    ⊢ ∼(σ.relabel .inl =' τ.relabel .inl) := sorry

abbrev tuple3 (σ τ μ : C) : C := pair (pair σ τ) μ

lemma tuple3_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) : IsInΓ (tuple3 σ τ μ) :=
  IsInΓ.pair (IsInΓ.pair hσ hτ) hμ

abbrev tuple4 (σ τ μ ν : C) : C := pair (tuple3 σ τ μ) ν

lemma tuple4_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) (hν : IsInΓ ν) :
    IsInΓ (tuple4 σ τ μ ν) := IsInΓ.pair (tuple3_isInΓ hσ hτ hμ) hν

abbrev tuple5 (σ τ μ ν ξ : C) : C := pair (tuple4 σ τ μ ν) ξ

lemma tuple5_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) (hν : IsInΓ ν) (hξ : IsInΓ ξ) :
    IsInΓ (tuple5 σ τ μ ν ξ) := IsInΓ.pair (tuple4_isInΓ hσ hτ hμ hν) hξ

abbrev tuple6 (σ τ μ ν ξ ζ : C) : C := pair (tuple5 σ τ μ ν ξ) ζ

lemma tuple6_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) (hν : IsInΓ ν) (hξ : IsInΓ ξ)
    (hζ : IsInΓ ζ) : IsInΓ (tuple6 σ τ μ ν ξ ζ) := IsInΓ.pair (tuple5_isInΓ hσ hτ hμ hν hξ) hζ

abbrev tuple7 (σ τ μ ν ξ ζ η : C) : C := pair (tuple6 σ τ μ ν ξ ζ) η

lemma tuple7_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) (hν : IsInΓ ν) (hξ : IsInΓ ξ)
    (hζ : IsInΓ ζ) (hη : IsInΓ η) : IsInΓ (tuple7 σ τ μ ν ξ ζ η) :=
  IsInΓ.pair (tuple6_isInΓ hσ hτ hμ hν hξ hζ) hη

def Code : Type := {τ : C // IsInΓ τ}

namespace Code

abbrev Mem : Code := ⟨pair (.func ∅' Fin.elim0) (.func ∅' Fin.elim0),
  by apply IsInΓ.pair <;> apply IsInΓ.isInΓ0 <;> apply IsInΓ0.empty⟩

abbrev Enlarge : Code := ⟨tuple3 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0),
  tuple3_isInΓ (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

abbrev Eq : Code :=
  ⟨tuple4 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0),
  tuple4_isInΓ (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
  (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

abbrev Or : Code :=
  ⟨tuple5 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0)
    (.func ∅' Fin.elim0), tuple5_isInΓ (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

abbrev Neg : Code :=
  ⟨tuple6 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0)
    (.func ∅' Fin.elim0) (.func ∅' Fin.elim0), tuple6_isInΓ (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

abbrev Ex : Code :=
  ⟨tuple7 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0)
    (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0), tuple7_isInΓ
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

def Term : Lang.Term (α : Type) → Code
| .var x => sorry
| @Term.func _ _ 0 f ts => ⟨.func ∅' Fin.elim0, IsInΓ.isInΓ0 IsInΓ0.empty⟩
| @Term.func _ _ 2 f ts => ⟨pair (Term (ts 1)).1 (Term (ts 2)).1,
    IsInΓ.pair ((Term (ts 1)).2) (Term (ts 2)).2⟩

def Formula : Lang.BoundedFormula (α : Type) n → Code
| .falsum => ⟨pair Neg.1 (tuple3 Eq.1 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0)),
  IsInΓ.pair Neg.2 (tuple3_isInΓ Eq.2 (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty))⟩ -- ¬ (0 = 0)
| .equal σ τ => ⟨tuple3 Eq.1 (Term σ).1 (Term τ).1, tuple3_isInΓ Eq.2 (Term σ).2 (Term τ).2⟩
| .rel (l := 2) _ ts => ⟨tuple3 Mem.1 (Term (ts 1)).1 (Term (ts 2)).1,
  tuple3_isInΓ Mem.2 (Term (ts 1)).2 (Term (ts 2)).2⟩
| .imp φ ψ => ⟨tuple3 Or.1 (pair Neg.1 (Formula φ).1) (Formula ψ).1,
  tuple3_isInΓ Or.2 (IsInΓ.pair Neg.2 (Formula φ).2) (Formula ψ).2⟩
| .all φ =>
  ⟨pair Neg.1 (tuple3 Ex.1 (Term (α := (α ⊕ Fin (n+1))) (&n)).1 (pair Neg.1 (Formula φ).1)),
  IsInΓ.pair Neg.2 (tuple3_isInΓ Ex.2 (Term (α := (α ⊕ Fin (n+1))) (&n)).2
  (IsInΓ.pair Neg.2 (Formula φ).2))⟩

end Code
end HF
