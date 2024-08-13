import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

open FirstOrder Language BoundedFormula

/-!
# The language and logic calculus of the theory of hereditarily finite sets

In this file, parts of Sections 1 and 4 of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness
Theorems' are formalised. It systematically presents the language and logic calculus of the
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
def Axiom1 : Lang.Formula (Fin 1) :=
(.var (.inl 0) =' (.func ∅' Fin.elim0)) ⇔ ∀' ∼(&0 ∈' .var (.inl 0))

/-- HF2: z = x ◁ y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y -/
def Axiom2 : Lang.Formula (Fin 3) :=
(.var (.inl 0) =' (.func ◁' ![.var (.inl 1), .var (.inl 2)]))
⇔ ∀' ((&0 ∈' .var (.inl 0)) ⇔ ((&0 ∈' .var (.inl 1)) ⊔ (&0 =' .var (.inl 2))))

/-- HF3: (α(∅) ∧ ∀ x y, α(x) → α(y) → α(x ◁ y)) → ∀ x α(x) -/
def Axiom3 (n) (α : Lang.BoundedFormula (Fin n) 1 ) : Lang.Formula (Fin n) :=
    ((∀' ((&0 =' .func ∅' Fin.elim0) ⟹ α))
    ⊓ (∀' ∀' ((α.liftAt 1 1 ⊓ (α.liftAt 1 0))
    ⟹ (∀' ((&2 =' .func ◁' ![&0, &1]) ⟹ α.liftAt 2 0)))))
    ⟹ ∀' α

def Theory :  Set (Σ n, Lang.Formula (Fin n)) :=
{⟨1, Axiom1⟩, ⟨3, Axiom2⟩} ∪ ⋃ (n), (⋃ (α : Lang.BoundedFormula (Fin n) 1), {⟨n, Axiom3 n α⟩})

namespace Bool

/-- Boolean axiom 1: φ → φ -/
def Axiom1 (φ : Lang.Formula (Fin n)) : Lang.Formula (Fin n) := φ ⟹ φ

/-- Boolean axiom 2: φ → φ ∨ ψ -/
def Axiom2 (φ ψ: Lang.Formula (Fin n)) : Lang.Formula (Fin n) := φ ⟹ (φ ⊔ ψ)

/-- Boolean axiom 3: φ ∨ φ → φ -/
def Axiom3 (φ : Lang.Formula (Fin n)) : Lang.Formula (Fin n) := (φ ⊔ φ) ⟹ φ

/-- Boolean axiom 4: φ ∨ (ψ ∨ μ) → (φ ∨ ψ) ∨ μ -/
def Axiom4 (φ ψ μ : Lang.Formula (Fin n)) : Lang.Formula (Fin n) := (φ ⊔ (ψ ⊔ μ)) ⟹ ((φ ⊔ ψ) ⊔ μ)

/-- Boolean axiom 5: (φ ∨ ψ) ∧ (¬φ ∨ μ) → ψ ∨ μ -/
def Axiom5 (φ ψ μ : Lang.Formula (Fin n)) : Lang.Formula (Fin n) := ((φ ⊔ ψ) ⊓ (∼φ ⊔ μ)) ⟹ (ψ ⊔ μ)

def Theory : Set (Σ n, Lang.Formula (Fin n)) :=
    ⋃ (n),
    ((⋃ (φ : Lang.Formula (Fin n)), (⋃ (ψ : Lang.Formula (Fin n)), (⋃ (μ : Lang.Formula (Fin n)),
    {⟨n, Axiom1 φ⟩, ⟨n, Axiom2 φ ψ⟩, ⟨n, Axiom3 φ⟩, ⟨n, Axiom4 φ ψ μ⟩, ⟨n, Axiom5 φ ψ μ⟩}))))

end Bool

namespace Spec

/-- Specialization axiom: For every formula φ and every xᵢ : φ → ∃ xᵢ φ -/
def Axiom1 (φ : Lang.BoundedFormula (Fin n) 1) : Lang.Formula (Fin n) :=
    ∀' (φ ⟹ ∃' φ.liftAt 1 0)

def Theory : Set (Σ n, Lang.Formula (Fin n)) :=
  ⋃ (n), (⋃ (φ : Lang.BoundedFormula (Fin n) 1), {⟨n, Axiom1 φ⟩})

end Spec

namespace Equality

/-- Equality axiom 1: x = x -/
def Axiom1 : Lang.Formula (Fin 1) := .var (.inl 0) =' .var (.inl 0)

/-- Equality axiom 2: (x₁ = x₂) ∧ (x₃ = x₄) → [(x₁ = x₃) → (x₂ → x₄)]  -/
def Axiom2: Lang.Formula (Fin 4) :=
    ((.var (.inl 0) =' .var (.inl 1)) ⊓ (.var (.inl 2) =' .var (.inl 3)))
    ⟹ ((.var (.inl 0) =' .var (.inl 2)) ⟹ (.var (.inl 1) =' .var (.inl 3)))

/-- Equality axiom 3: (x₁ = x₂) ∧ (x₃ = x₄) → [(x₁ ∈ x₃) → (x₂ ∈ x₄)]  -/
def Axiom3: Lang.Formula (Fin 4) :=
    ((.var (.inl 0) =' .var (.inl 1)) ⊓ (.var (.inl 2) =' .var (.inl 0)))
    ⟹ ((.var (.inl 0) ∈' .var (.inl 2)) ⟹ (.var (.inl 1) ∈' .var (.inl 3)))

/-- Equality axiom 4: (x₁ = x₂) ∧ (x₃ = x₄) → (x₁ ◁ x₃ = x₂ ◁ x₄)  -/
def Axiom4: Lang.Formula (Fin 4) :=
    ((.var (.inl 0) =' .var (.inl 1)) ⊓ (.var (.inl 2) =' .var (.inl 3)))
    ⟹ ((.func ◁' ![.var (.inl 0), .var (.inl 2)]) =' (.func ◁' ![.var (.inl 1), .var (.inl 3)]))

def Theory : Set (Σ n, Lang.Formula (Fin n)) :=
    {⟨1, Axiom1⟩, ⟨4, Axiom2⟩, ⟨4, Axiom3⟩, ⟨4, Axiom4⟩}

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

-- missing substitution and existential quantifier rules
inductive thm : Set (Σ n, Lang.Formula (Fin n)) → ℕ → Lang.Formula (Fin n) → Prop
| Hyp : ⟨n, φ⟩  ∈ T → thm T n φ
| Ax : ⟨n, φ⟩ ∈ Theory → thm T n φ
| Bool : ⟨n, φ⟩ ∈ Bool.Theory → thm T n φ
| Spec : ⟨n, φ⟩ ∈ Spec.Theory → thm T n φ
| Eq : ⟨n, φ⟩ ∈ Equality.Theory → thm T n φ
| MP (ψ : Lang.Formula (Fin n)) : thm T n (ψ ⟹ φ) → thm T n ψ → thm T n φ

abbrev thm' (T : Set (Σ n, Lang.Formula (Fin n))) (φ : Lang.Formula (Fin n)) : Prop :=
  ∃ n, thm T n φ

infix:51 "⊢" => thm'

prefix:51 "⊢" => thm' {}

@[simp] lemma deduc_iff (T : Set (Σ n, Lang.Formula (Fin n))) (φ : Lang.Formula (Fin n)) :
    T ⊢ φ ↔ ∃ n, thm T n φ := by rfl

@[simp] lemma thm_iff (φ : Lang.Formula (Fin n)) : ⊢ φ ↔ ∃ n, thm {} n φ := by rfl

-- not sure if this will be necessary
theorem deduction_theorem (T : Set (Σ n, Lang.Formula (Fin n))) (φ ψ : Lang.Formula (Fin n))
   (h : T ∪ {⟨n, φ⟩} ⊢ ψ) : T ⊢ (φ ⟹ ψ) := by
  -- need induction on proof
  sorry

example : ⊢ Equality.Axiom1 := by
  simp only [thm_iff]
  use 1
  apply thm.Eq
  simp [Equality.Theory]

example : ⊢ Axiom3 0 (&0 =' &0) := by
  simp only [Fin.isValue, Function.comp_apply, thm_iff]
  use 0
  apply thm.Ax
  simp [Theory]

example : ⊢ Bool.Axiom1 (Axiom1) := by
  simp only [thm_iff]
  use 1
  apply thm.Bool
  simp only [Bool.Theory, Set.mem_iUnion, Set.mem_insert_iff, Sigma.mk.inj_iff,
    Set.mem_singleton_iff]
  use 1; use Axiom1
  simp

example (φ : Lang.Formula (Fin 1)) : ⊢ (Axiom1 ⟹ φ) ⟹ φ := by
  apply deduction_theorem
  simp only [Set.union_singleton, insert_emptyc_eq, deduc_iff]
  use 1
  apply thm.MP Axiom1
  · apply thm.Hyp; simp
  · apply thm.Ax
    simp [Theory]

-- example (t : Lang.Term (Empty ⊕ Fin 0)) : ⊢ t =' t := by
--   sorry

end HF
