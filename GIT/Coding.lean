import GIT.Model

/-!
# Coding

In this file, part of Section 1 of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness
Theorems' is formalised. It constructs the coding of terms and formulas in the language of HF.

## Main definitions
* `HF.C.IsInΓ0` : The Γ₀ family of constant terms.
* `HF.C.IsInΓ` : The Γ family of constant terms, where all codes belong to.
* `HF.Code` : The code subtype, i.e. the Γ subtype.
* `HF.Code.Term` : The code of a term in the lanuage of HF.
* `HF.Code.Formula` : The code of a formula in the language of HF.

## Implementation notes
* The code of the first-order formula 'False' is implemented as the code of '¬(∅ = ∅)', see `falsum`
  in `HF.Code.Formula`.
* To formalise the coding of terms and formulas, we assume α is a Fintype, i.e. the number of
  free variables is finite. This suffices for the rest of the formalisations.

## References
* S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
  mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.

## TO DO
* If it turns out to be necessary, prove `HF.C.ne_of_isInΓ_and_distinct`.
-/

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

namespace C

/-- Ordered pair of constant terms. -/
abbrev pair (σ τ : C) : C :=
  .func ◁' ![(.func ◁' ![.func ∅' Fin.elim0, .func ◁' ![.func ∅' Fin.elim0, σ] ]),
  .func ◁' ![.func ◁' ![.func ∅' Fin.elim0, σ] ,τ] ]

/-- The Γ₀ family of constant terms. -/
inductive IsInΓ0 : C → Prop where
| empty : IsInΓ0 (.func ∅' Fin.elim0)
| enlarge (hσ : IsInΓ0 σ) : IsInΓ0 (.func ◁' ![σ, σ])

/-- The Γ family of constant terms, where all codes belong to. -/
inductive IsInΓ : C → Prop where
| isInΓ0 (h : IsInΓ0 σ) : IsInΓ σ
| pair (hσ : IsInΓ σ) (hτ : IsInΓ τ) : IsInΓ (pair σ τ)

lemma ne_of_isInΓ_and_distinct (σ τ : C) (hσ : IsInΓ σ) (hτ : IsInΓ τ) (h : σ ≠ τ) :
    ⊢ (∼(σ.relabel .inl =' τ.relabel .inl) : Lang.Sentence) := sorry

/-- Ordered 3-tuple of constant terms. -/
abbrev tuple3 (σ τ μ : C) : C := pair (pair σ τ) μ

lemma tuple3_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) : IsInΓ (tuple3 σ τ μ) :=
  IsInΓ.pair (IsInΓ.pair hσ hτ) hμ

/-- Ordered 4-tuple of constant terms. -/
abbrev tuple4 (σ τ μ ν : C) : C := pair (tuple3 σ τ μ) ν

lemma tuple4_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) (hν : IsInΓ ν) :
    IsInΓ (tuple4 σ τ μ ν) := IsInΓ.pair (tuple3_isInΓ hσ hτ hμ) hν

/-- Ordered 5-tuple of constant terms. -/
abbrev tuple5 (σ τ μ ν ξ : C) : C := pair (tuple4 σ τ μ ν) ξ

lemma tuple5_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) (hν : IsInΓ ν) (hξ : IsInΓ ξ) :
    IsInΓ (tuple5 σ τ μ ν ξ) := IsInΓ.pair (tuple4_isInΓ hσ hτ hμ hν) hξ

/-- Ordered 6-tuple of constant terms. -/
abbrev tuple6 (σ τ μ ν ξ ζ : C) : C := pair (tuple5 σ τ μ ν ξ) ζ

lemma tuple6_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) (hν : IsInΓ ν) (hξ : IsInΓ ξ)
    (hζ : IsInΓ ζ) : IsInΓ (tuple6 σ τ μ ν ξ ζ) := IsInΓ.pair (tuple5_isInΓ hσ hτ hμ hν hξ) hζ

/-- Ordered 7-tuple of constant terms. -/
abbrev tuple7 (σ τ μ ν ξ ζ η : C) : C := pair (tuple6 σ τ μ ν ξ ζ) η

lemma tuple7_isInΓ (hσ : IsInΓ σ) (hτ : IsInΓ τ) (hμ : IsInΓ μ) (hν : IsInΓ ν) (hξ : IsInΓ ξ)
    (hζ : IsInΓ ζ) (hη : IsInΓ η) : IsInΓ (tuple7 σ τ μ ν ξ ζ η) :=
  IsInΓ.pair (tuple6_isInΓ hσ hτ hμ hν hξ hζ) hη

/-- Function from a natural number to its corresponding ordinal, which is a constant term. -/
def Ord : ℕ → C
| 0 => .func ∅' Fin.elim0
| Nat.succ n => .func ◁' ![(Ord n), (Ord n)]

lemma ord_isInΓ (n : ℕ) : IsInΓ (Ord n) := by
  apply IsInΓ.isInΓ0
  induction n with
  | zero => apply IsInΓ0.empty
  | succ n h => exact IsInΓ0.enlarge h

end C

open C

/-- The code subtype, i.e. the Γ subtype. -/
def Code : Type := {τ : C // IsInΓ τ}

namespace Code

/-- The code of the membership symbol. -/
abbrev Mem : Code := ⟨pair (.func ∅' Fin.elim0) (.func ∅' Fin.elim0),
  by apply IsInΓ.pair <;> apply IsInΓ.isInΓ0 <;> apply IsInΓ0.empty⟩

/-- The code of the enlargement symbol. -/
abbrev Enlarge : Code := ⟨tuple3 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0),
  tuple3_isInΓ (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

/-- The code of the equality symbol. -/
abbrev Eq : Code :=
  ⟨tuple4 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0),
  tuple4_isInΓ (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
  (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

/-- The code of the disjunction symbol. -/
abbrev Or : Code :=
  ⟨tuple5 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0)
    (.func ∅' Fin.elim0), tuple5_isInΓ (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

/-- The code of the negation symbol. -/
abbrev Neg : Code :=
  ⟨tuple6 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0)
    (.func ∅' Fin.elim0) (.func ∅' Fin.elim0), tuple6_isInΓ (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

/-- The code of the existential quantifier symbol. -/
abbrev Ex : Code :=
  ⟨tuple7 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0)
    (.func ∅' Fin.elim0) (.func ∅' Fin.elim0) (.func ∅' Fin.elim0), tuple7_isInΓ
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty)
    (IsInΓ.isInΓ0 IsInΓ0.empty)⟩

/-- The code of a term in the lanuage of HF. -/
def Term [Fintype α] : Lang.Term (α : Type) → Code
| .var i => ⟨Ord ((Fintype.equivFin α) i), ord_isInΓ ((Fintype.equivFin α) i)⟩
| @Term.func _ _ 0 _ _ => ⟨.func ∅' Fin.elim0, IsInΓ.isInΓ0 IsInΓ0.empty⟩
| @Term.func _ _ 2 _ ts => ⟨tuple3 Enlarge.1 (Term (ts 1)).1 (Term (ts 2)).1,
    tuple3_isInΓ Enlarge.2 ((Term (ts 1)).2) (Term (ts 2)).2⟩

/-- The code of a formula in the language of HF. -/
def Formula [Fintype α] : Lang.BoundedFormula (α : Type) n → Code
| .falsum => ⟨pair Neg.1 (tuple3 Eq.1 (.func ∅' Fin.elim0) (.func ∅' Fin.elim0)),
  IsInΓ.pair Neg.2 (tuple3_isInΓ Eq.2 (IsInΓ.isInΓ0 IsInΓ0.empty) (IsInΓ.isInΓ0 IsInΓ0.empty))⟩
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
