import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

open FirstOrder Language BoundedFormula

/-!
# The language and logical calculus of the theory of hereditarily finite sets

In this file, parts of Sections 1 and 4 of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness
Theorems' are formalised. It systematically presents the language and logical calculus of the
theory of hereditarily finite sets.

## Main results

- `...`: ...

## Notation

- `◁` : enlarging, see `HF.Axiom2`.

## References

S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.
-/

namespace HF

/-- The first-order language of HF. -/
def Lang : Language.{0, 0} where
  Functions :=
  fun
  | 0 => PUnit -- We have one 0-ary function, i.e. a constant term, "for the empty set".
  | 1 => Empty -- We have no 1-ary functions.
  | 2 => PUnit -- We have one 2-ary function "for enlargement".
  | _ + 3 => Empty -- We have no n-ary functions for n > 2.
  Relations :=
  fun
  | 0 => Empty -- We have no 0-ary relations.
  | 1 => Empty -- We have no unary relations.
  | 2 => PUnit -- We have one binary relation for "membership"
  | _ + 3 => Empty -- We have no n-ary relations for n > 2.

/-- Empty set: constant symbol. -/
abbrev Lang.emptySetSymbol : Lang.Functions 0 := PUnit.unit

local notation "∅'" => Lang.emptySetSymbol

/-- Enlargement: 2-ary function symbol. -/
abbrev Lang.enlargementSymbol : Lang.Functions 2 := PUnit.unit

local notation " ◁' " => Lang.enlargementSymbol

/-- Membership: 2-ary relation symbol. -/
abbrev Lang.membershipSymbol : Lang.Relations 2 := PUnit.unit

local notation t " ∈' " s => Lang.membershipSymbol.boundedFormula ![t, s]

/-- HF1: z = ∅ ↔ ∀ x, ¬(x ∈ z) -/
def Axiom1 (t : Lang.Term α) : Lang.Formula α :=
  (t.relabel .inl =' (.func ∅' Fin.elim0)) ⇔ ∀' ∼(&0 ∈' t.relabel .inl)


/-- HF2: z = x ◁ y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y -/
def Axiom2 (t1 t2 t3 : Lang.Term α) : Lang.Formula α :=
  (t1.relabel .inl =' (.func ◁' ![t2.relabel .inl, t3.relabel .inl]))
  ⇔ ∀' ((&0 ∈' t1.relabel .inl) ⇔ ((&0 ∈' t2.relabel .inl) ⊔ (&0 =' t3.relabel .inl)))

/-- HF3: (α(∅) ∧ ∀ x y, α(x) → α(y) → α(x ◁ y)) → ∀ x α(x) -/
def Axiom3 (φ : Lang.BoundedFormula α 1 ) : Lang.Formula α :=
  ((∀' ((&0 =' .func ∅' Fin.elim0) ⟹ φ))
  ⊓ (∀' ∀' ((φ.liftAt 1 1 ⊓ (φ.liftAt 1 0))
  ⟹ (∀' ((&2 =' .func ◁' ![&0, &1]) ⟹ φ.liftAt 2 0)))))
  ⟹ ∀' φ

def Theory :  Set (Lang.Formula α) :=
  (⋃ (t : Lang.Term α), {Axiom1 t}) ∪
  (⋃ (t1 : Lang.Term α),(⋃ (t2 : Lang.Term α), (⋃ (t3 : Lang.Term α), {Axiom2 t1 t2 t3}))) ∪
  (⋃ (φ : Lang.BoundedFormula α 1), {Axiom3 φ})

namespace Bool

/-- Boolean axiom 1: φ → φ -/
def Axiom1 (φ : Lang.Formula α) : Lang.Formula α := φ ⟹ φ

/-- Boolean axiom 2: φ → φ ∨ ψ -/
def Axiom2 (φ ψ: Lang.Formula α) : Lang.Formula α := φ ⟹ (φ ⊔ ψ)

/-- Boolean axiom 3: φ ∨ φ → φ -/
def Axiom3 (φ : Lang.Formula α) : Lang.Formula α := (φ ⊔ φ) ⟹ φ

/-- Boolean axiom 4: φ ∨ (ψ ∨ μ) → (φ ∨ ψ) ∨ μ -/
def Axiom4 (φ ψ μ : Lang.Formula α) : Lang.Formula α := (φ ⊔ (ψ ⊔ μ)) ⟹ ((φ ⊔ ψ) ⊔ μ)

/-- Boolean axiom 5: (φ ∨ ψ) ∧ (¬φ ∨ μ) → ψ ∨ μ -/
def Axiom5 (φ ψ μ : Lang.Formula α) : Lang.Formula α := ((φ ⊔ ψ) ⊓ (∼φ ⊔ μ)) ⟹ (ψ ⊔ μ)

def Theory : Set (Lang.Formula α) :=
  (⋃ (φ : Lang.Formula α), {Axiom1 φ}) ∪
  (⋃ (φ : Lang.Formula α), (⋃ (ψ : Lang.Formula α), {Axiom2 φ ψ})) ∪
  (⋃ (φ : Lang.Formula α), {Axiom3 φ}) ∪
  (⋃ (φ : Lang.Formula α), (⋃ (ψ : Lang.Formula α), (⋃ (μ : Lang.Formula α), {Axiom4 φ ψ μ}))) ∪
  (⋃ (φ : Lang.Formula α), (⋃ (ψ : Lang.Formula α), (⋃ (μ : Lang.Formula α), {Axiom5 φ ψ μ})))

end Bool

namespace Spec

-- not 100% sure about this one
/-- Specialization axiom: For every formula φ and every xᵢ : φ → ∃ xᵢ φ -/
def Axiom (φ : Lang.BoundedFormula α 1) : Lang.Formula α :=
    ∀' (φ ⟹ ∃' φ.liftAt 1 0)

def Theory : Set (Lang.Formula α) :=
  ⋃ (φ : Lang.BoundedFormula α 1), {Axiom φ}

end Spec

namespace Equality

/-- Equality axiom 1: x = x -/
def Axiom1 (t : Lang.Term α) : Lang.Formula α := t.relabel .inl =' t.relabel .inl

/-- Equality axiom 2: (x₁ = x₂) ∧ (x₃ = x₄) → [(x₁ = x₃) → (x₂ → x₄)]  -/
def Axiom2 (t1 t2 t3 t4 : Lang.Term α) : Lang.Formula α :=
  ((t1.relabel .inl =' t2.relabel .inl) ⊓ (t3.relabel .inl =' t4.relabel .inl))
  ⟹ ((t1.relabel .inl =' t3.relabel .inl) ⟹ (t2.relabel .inl =' t4.relabel .inl))

/-- Equality axiom 3: (x₁ = x₂) ∧ (x₃ = x₄) → [(x₁ ∈ x₃) → (x₂ ∈ x₄)]  -/
def Axiom3 (t1 t2 t3 t4 : Lang.Term α) : Lang.Formula α :=
  ((t1.relabel .inl =' t2.relabel .inl) ⊓ (t3.relabel .inl =' t4.relabel .inl))
  ⟹ ((t1.relabel .inl ∈' t3.relabel .inl) ⟹ (t2.relabel .inl ∈' t4.relabel .inl))

/-- Equality axiom 4: (x₁ = x₂) ∧ (x₃ = x₄) → (x₁ ◁ x₃ = x₂ ◁ x₄)  -/
def Axiom4 (t1 t2 t3 t4 : Lang.Term α) : Lang.Formula α :=
  ((t1.relabel .inl =' t2.relabel .inl) ⊓ (t3.relabel .inl =' t4.relabel .inl))
  ⟹ (.func ◁' ![t1.relabel .inl, t3.relabel .inl] =' .func ◁' ![t2.relabel .inl, t4.relabel .inl])

def Theory :  Set (Lang.Formula α) :=
  (⋃ (t : Lang.Term α), {Axiom1 t}) ∪
  (⋃ (t1 : Lang.Term α),(⋃ (t2 : Lang.Term α), (⋃ (t3 : Lang.Term α), (⋃ (t4 : Lang.Term α),
  {Axiom2 t1 t2 t3 t4})))) ∪
  (⋃ (t1 : Lang.Term α),(⋃ (t2 : Lang.Term α), (⋃ (t3 : Lang.Term α), (⋃ (t4 : Lang.Term α),
  {Axiom3 t1 t2 t3 t4})))) ∪
  (⋃ (t1 : Lang.Term α),(⋃ (t2 : Lang.Term α), (⋃ (t3 : Lang.Term α), (⋃ (t4 : Lang.Term α),
  {Axiom4 t1 t2 t3 t4}))))

end Equality

-- inductive Theorem : Lang.Theory → Lang.Sentence → Prop
-- | Hyp : φ ∈ T → Theorem T φ
-- | Ax : φ ∈ Theory → Theorem T φ
-- | Bool : φ ∈ Bool.Theory → Theorem T φ
-- | Spec : φ ∈ Spec.Theory → Theorem T φ
-- | Eq : φ ∈ Equality.Theory → Theorem T φ
-- | MP (ψ) : Theorem T (ψ ⟹ φ) → Theorem T ψ → Theorem T φ
-- | Subst (φ : Lang.BoundedFormula Empty 1) (t : Lang.Term (Empty ⊕ Fin 0)) :
--     Theorem T (∀' φ) → Theorem T (sorry) -- not sure how to do this (and if type of t is correct)
-- | Exists (φ : Lang.BoundedFormula Empty 2) (ψ : Lang.BoundedFormula Empty 1) :
--     Theorem T (∀' ∀' (φ ⟹ ψ)) → sorry → Theorem T (∀' (∃' φ) ⟹ ψ)

-- missing substitution and ∃-intro deduction rules
inductive prf : Set (Lang.Formula (α)) → Lang.Formula α → Prop
| Hyp : φ ∈ T → prf T φ
| Ax : φ ∈ Theory → prf T φ
| Bool : φ ∈ Bool.Theory → prf T φ
| Spec : φ ∈ Spec.Theory → prf T φ
| Eq : φ ∈ Equality.Theory → prf T φ
| MP (ψ : Lang.Formula α) (h1 : prf T (ψ ⟹ φ)) (h2 : prf T ψ) : prf T φ
-- Substition: from φ deduce φ (x/t) for any term t that is substitutable for x in φ
-- ∃-introduction: from φ → ψ deduce ∃ x φ → ψ provided x is not free in ψ

infix:51 "⊢" => prf

prefix:51 "⊢" => prf {}

example : ⊢ Axiom3 (α := Fin 0) (&0 =' &0) := by
  apply prf.Ax
  simp [Theory]

example (t : Lang.Term Empty) : ⊢ Bool.Axiom1 (Axiom1 t) := by
  apply prf.Bool
  simp [Bool.Theory]

example (t : Lang.Term (Empty ⊕ Fin 0)) : ⊢ t.relabel .inl =' t.relabel .inl := by
  apply prf.Eq
  simp [Equality.Theory]
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply Exists.intro
  · apply Eq.refl

abbrev models (s) [Lang.Structure s] (φ : Lang.Formula α) : Prop := ∀ (c : α → s), φ.Realize c

infixl:51 " ⊧ " => models

class Model (s) [Lang.Structure s] : Prop where
  realize_of_mem : ∀ (φ : Lang.Formula α), φ ∈ Theory → s ⊧ φ

theorem completeness (φ : Lang.Formula α) :
  (∀ (s : Type u) [Lang.Structure s] [Model s], s ⊧ φ) → ⊢ φ := by
  sorry

example (t : Lang.Term α) : ⊢ ∼(t.relabel .inl ∈' t.relabel .inl) := by
  -- apply completeness
  sorry

end HF
