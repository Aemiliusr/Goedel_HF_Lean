import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

open FirstOrder Language BoundedFormula

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

/-- HF1: ∀ z, z = ∅ ↔ ∀ x, ¬(x ∈ z) -/
def Axiom1 : Lang.Sentence :=
∀' (&0 =' (.func ∅' Fin.elim0)) ⇔ ∀' ∼(&0 ∈' &1)

/-- HF2: ∀ z, ∀ x, ∀ y, z = x ◁ y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y -/
def Axiom2 : Lang.Sentence :=
∀' ∀' ∀'
  (&0 =' (.func ◁' ![&1, &2])) ⇔
  ∀' ((&3 ∈' &0) ⇔ ((&3 ∈' &1) ⊔ (&3 ∈' &2)))

/-- HF3: (α(∅) ∧ ∀ x y, α(x) → α(y) → α(x ◁ y)) → ∀ x α(x) -/
def Axiom3 (n : ℕ) (α : Lang.BoundedFormula (Fin n) 1) : Lang.Sentence := sorry

-- this is incomplete because α needs to be BoundedFormula (Fin n) 1
/-- HF3: (α(∅) ∧ ∀ x y, α(x) → α(y) → α(x ◁ y)) → ∀ x α(x) -/
def Axiom3' (α : Lang.Formula (Fin 1)) : Lang.Sentence :=
(α.subst ![.func ∅' Fin.elim0] ⊓
∀' ∀'
((α.subst ![.var 0] |>.relabel ![.inr 0]) ⊓ (α.subst ![.var 1] |>.relabel ![.inr 1]) ⟹
  (α.subst ![ .func ◁' ![.var 0, .var 1] ] |>.relabel .inr))) ⟹
  ∀' (α.subst ![.var 0] |>.relabel ![.inr 0])

def Theory : Lang.Theory :=
{Axiom1, Axiom2} ∪ ⋃ (α : Lang.Formula (Fin 1)), {Axiom3' α}

namespace Bool

/-- Boolean axiom 1: φ → φ -/
def Axiom1 (φ : Lang.Sentence) : Lang.Sentence := φ ⟹ φ

/-- Boolean axiom 2: φ → φ ∨ ψ -/
def Axiom2 (φ ψ : Lang.Sentence) : Lang.Sentence := φ ⟹ (φ ⊔ ψ)

/-- Boolean axiom 3: φ ∨ φ → φ -/
def Axiom3 (φ : Lang.Sentence) : Lang.Sentence := (φ ⊔ φ) ⟹ φ

/-- Boolean axiom 4: φ ∨ (ψ ∨ μ) → (φ ∨ ψ) ∨ μ -/
def Axiom4 (φ ψ μ : Lang.Sentence) : Lang.Sentence := (φ ⊔ (ψ ⊔ μ)) ⟹ ((φ ⊔ ψ) ⊔ μ)

/-- Boolean axiom 5: (φ ∨ ψ) ∧ (¬φ ∨ μ) → ψ ∨ μ -/
def Axiom5 (φ ψ μ : Lang.Sentence) : Lang.Sentence := ((φ ⊔ ψ) ⊓ (∼φ ⊔ μ)) ⟹ (ψ ⊔ μ)

-- missing the other axioms
def Theory : Lang.Theory := (⋃ (φ : Lang.Sentence), {Axiom1 φ, Axiom3 φ})

end Bool

inductive Theorem (T : Lang.Theory) (φ : Lang.Sentence) : Prop
| Ax : φ ∈ Theory → Theorem T φ
| Bool : φ ∈ Bool.Theory → Theorem T φ

infixl:55 "⊢" => Theorem

example : Theory ⊢ Axiom1 := by apply Theorem.Ax ; simp [Theory]

end HF
