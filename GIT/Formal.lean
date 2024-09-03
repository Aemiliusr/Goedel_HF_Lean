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

notation "∅'" => Lang.emptySetSymbol

/-- Enlargement: 2-ary function symbol. -/
abbrev Lang.enlargementSymbol : Lang.Functions 2 := PUnit.unit

notation " ◁' " => Lang.enlargementSymbol

/-- Membership: 2-ary relation symbol. -/
abbrev Lang.membershipSymbol : Lang.Relations 2 := PUnit.unit

notation t " ∈' " s => Lang.membershipSymbol.boundedFormula ![t, s]

/-- HF1: z = ∅ ↔ ∀ x, ¬(x ∈ z) -/
def Axiom1 : Lang.Sentence :=
  ∀' ((&0 =' (.func ∅' Fin.elim0)) ⇔ ∀' ∼(&1 ∈' &0))

/-- HF2: z = x ◁ y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y -/
def Axiom2 : Lang.Sentence :=
  ∀' ∀' ∀' ((&0 =' .func ◁' ![&1, &2]) ⇔ (∀' ((&3 ∈' &0) ⇔ ((&3 ∈' &1) ⊔ (&3 =' &2)))))

/-- HF3: (α(∅) ∧ ∀ x y, α(x) → α(y) → α(x ◁ y)) → ∀ x α(x) -/
def Axiom3 (φ : Lang.BoundedFormula (α : Type) 1) : Lang.Formula α :=
  ((∀' ((&0 =' .func ∅' Fin.elim0) ⟹ φ))
  ⊓ (∀' ∀' ((φ.liftAt 1 1 ⊓ (φ.liftAt 1 0))
  ⟹ (∀' ((&2 =' .func ◁' ![&0, &1]) ⟹ φ.liftAt 2 0)))))
  ⟹ ∀' φ

def Theory : Lang.Theory := {Axiom1, Axiom2}

def Scheme : Set (Lang.Formula α) :=
  ⋃ (φ : Lang.BoundedFormula α 1), {Axiom3 φ}

namespace Bool

/-- Boolean axiom 1: φ → φ -/
def Axiom1 (φ : Lang.BoundedFormula α n) : Lang.BoundedFormula α n := φ ⟹ φ

/-- Boolean axiom 2: φ → φ ∨ ψ -/
def Axiom2 (φ ψ : Lang.BoundedFormula α n) : Lang.BoundedFormula α n := φ ⟹ (φ ⊔ ψ)

/-- Boolean axiom 3: φ ∨ φ → φ -/
def Axiom3 (φ : Lang.BoundedFormula α n) : Lang.BoundedFormula α n := (φ ⊔ φ) ⟹ φ

/-- Boolean axiom 4: φ ∨ (ψ ∨ μ) → (φ ∨ ψ) ∨ μ -/
def Axiom4 (φ ψ μ : Lang.BoundedFormula α n) : Lang.BoundedFormula α n :=
  (φ ⊔ (ψ ⊔ μ)) ⟹ ((φ ⊔ ψ) ⊔ μ)

/-- Boolean axiom 5: (φ ∨ ψ) ∧ (¬φ ∨ μ) → ψ ∨ μ -/
def Axiom5 (φ ψ μ : Lang.BoundedFormula α n) : Lang.BoundedFormula α n :=
  ((φ ⊔ ψ) ⊓ (∼φ ⊔ μ)) ⟹ (ψ ⊔ μ)

def Theory : Set (Lang.BoundedFormula α n) :=
  (⋃ (φ : Lang.BoundedFormula α n), {Axiom1 φ}) ∪
  (⋃ (φ : Lang.BoundedFormula α n), (⋃ (ψ : Lang.BoundedFormula α n), {Axiom2 φ ψ})) ∪
  (⋃ (φ : Lang.BoundedFormula α n), {Axiom3 φ}) ∪
  (⋃ (φ : Lang.BoundedFormula α n), (⋃ (ψ : Lang.BoundedFormula α n),
    (⋃ (μ : Lang.BoundedFormula α n), {Axiom4 φ ψ μ}))) ∪
  (⋃ (φ : Lang.BoundedFormula α n), (⋃ (ψ : Lang.BoundedFormula α n),
    (⋃ (μ : Lang.BoundedFormula α n), {Axiom5 φ ψ μ})))

end Bool

namespace Equality

/-- Equality axiom 1: x = x -/
def Axiom1 : Lang.Sentence := ∀' (&0 =' &0)

/-- Equality axiom 2: (x₁ = x₂) ∧ (x₃ = x₄) → [(x₁ = x₃) → (x₂ → x₄)]  -/
def Axiom2 : Lang.Sentence :=
  ∀' ∀' ∀' ∀' (((&0 =' &1) ⊓ (&2 =' &3)) ⟹ ((&0 =' &2) ⟹ (&1 =' &3)))

/-- Equality axiom 3: (x₁ = x₂) ∧ (x₃ = x₄) → [(x₁ ∈ x₃) → (x₂ ∈ x₄)]  -/
def Axiom3 : Lang.Sentence :=
  ∀' ∀' ∀' ∀' (((&0 =' &1) ⊓ (&2 =' &3)) ⟹ ((&0 ∈' &2) ⟹ (&1 ∈' &3)))

/-- Equality axiom 4: (x₁ = x₂) ∧ (x₃ = x₄) → (x₁ ◁ x₃ = x₂ ◁ x₄)  -/
def Axiom4 : Lang.Sentence :=
  ∀' ∀' ∀' ∀' (((&0 =' &1) ⊓ (&2 =' &3)) ⟹ (.func ◁' ![&0, &2] =' .func ◁' ![&1, &3]))

def Theory :  Lang.Theory := {Axiom1, Axiom2, Axiom3, Axiom4}

end Equality

inductive Prf (T : {α : Type} → {n : ℕ} → Set (Lang.BoundedFormula α n)) :
    {α : Type} → {n : ℕ} → Lang.BoundedFormula α n → Prop
| hyp : φ ∈ T → Prf T φ
| ax : φ ∈ Theory → Prf T φ
| induc : φ ∈ Scheme → Prf T φ
| bool : φ ∈ Bool.Theory → Prf T φ
| eq : φ ∈ Equality.Theory → Prf T φ
| spec (φ : Lang.BoundedFormula α (n + 1)) : Prf T φ → Prf T (∃' φ)
| mp (φ ψ : Lang.BoundedFormula α n) : Prf T (ψ ⟹ φ) → Prf T ψ → Prf T φ
| subst (φ : Lang.BoundedFormula α n) (f : α → Lang.Term β) : Prf T φ → Prf T (φ.subst f)
| exists_intro (φ : Lang.BoundedFormula α (n + 1)) (ψ : Lang.BoundedFormula α n) :
    Prf T (φ ⟹ ψ.liftAt 1 n) → Prf T (∃' φ ⟹ ψ)

prefix:51 "⊢" => Prf {}

abbrev models (S : Type) [Lang.Structure S] (φ : Lang.BoundedFormula α n) : Prop :=
  ∀ (v : α → S) (xs : Fin n → S), φ.Realize v xs

infixl:51 " ⊧ " => models

lemma models_iff_realize_of_sentence (S : Type) [Lang.Structure S] (φ : Lang.Sentence) :
    S ⊨ φ ↔ S ⊧ φ := by
  refine ⟨?_, fun a ↦ a default default⟩
  intros h v xs
  have : xs = default := by ext i; fin_cases i
  rwa [(Pi.uniqueOfIsEmpty fun _ ↦ S).uniq v, this]

lemma neg_models_iff_models_neg_of_sentence (S : Type) [Lang.Structure S] (φ : Lang.Sentence) :
    ¬S ⊧ φ ↔ S ⊧ ∼φ := by
  simp_rw [← models_iff_realize_of_sentence]
  exact Iff.symm (Sentence.realize_not S)

class Model (S : Type) where
  non_empty : Nonempty S
  struc : Lang.Structure S
  realize_of_mem_theory : ∀ (φ : Lang.Sentence), φ ∈ Theory → S ⊧ φ
  realize_of_mem_scheme : ∀ (φ : Lang.Formula α), φ ∈ Scheme → S ⊧ φ

instance (S : Type) [Model S] : Lang.Structure S := Model.struc

abbrev valid (φ : Lang.BoundedFormula α n) : Prop := ∀ (S : Type) [Model S], S ⊧ φ

prefix:51 " ⊧ " => valid

namespace soundness

lemma ax (h : φ ∈ Theory) : ⊧ φ := by
  intros _ inst v xs
  rcases inst with ⟨_, _, rel1, _⟩
  exact rel1 φ h v xs

lemma induc (h : φ ∈ Scheme) : ⊧ φ := by
  intros _ inst v xs
  rcases inst with ⟨_, _, _, rel2⟩
  exact rel2 φ h v xs

lemma bool (h : φ ∈ Bool.Theory) : ⊧ φ := by
  rcases h with ⟨⟨⟨ax1 | ax2⟩ | ax3⟩ | ax4⟩ | ax5
  · simp only [Set.iUnion_singleton_eq_range, Set.mem_range] at ax1
    rcases ax1 with ⟨φ, rfl⟩
    unfold Bool.Axiom1
    intros _ inst v xs
    simp
  · simp only [Set.iUnion_singleton_eq_range, Set.mem_iUnion, Set.mem_range] at ax2
    rcases ax2 with ⟨φ, μ, rfl⟩
    unfold Bool.Axiom2
    intros _ inst v xs
    simp_all
  · simp only [Set.iUnion_singleton_eq_range, Set.mem_range] at ax3
    rcases ax3 with ⟨φ, rfl⟩
    unfold Bool.Axiom3
    intros _ inst v xs
    simp
  · simp only [Set.iUnion_singleton_eq_range, Set.mem_iUnion, Set.mem_range] at ax4
    rcases ax4 with ⟨φ, ψ, μ, rfl⟩
    unfold Bool.Axiom4
    intros _ inst v xs
    aesop
  · simp only [Set.iUnion_singleton_eq_range, Set.mem_iUnion, Set.mem_range] at ax5
    rcases ax5 with ⟨φ, ψ, μ, rfl⟩
    unfold Bool.Axiom5
    intros _ inst v xs
    aesop

lemma eq (h : φ ∈ Equality.Theory) : ⊧ φ := by
  rcases h with ax1 | ax2 | ax3 | ax4
  · unfold Equality.Axiom1 at ax1
    intros _ inst v xs
    simp_all
  · unfold Equality.Axiom2 at ax2
    intros _ inst v xs
    simp_all
  · unfold Equality.Axiom3 at ax3
    intros _ inst v xs
    subst φ
    intros x y z w
    simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_imp, realize_inf,
      realize_bdEqual, Term.realize_var, Sum.elim_inr, Fin.snoc, Fin.val_zero, Nat.ofNat_pos,
      ↓reduceDIte, Fin.castSucc_castLT, Fin.coe_castLT, zero_lt_one, Nat.zero_eq, Fin.coe_fin_one,
      lt_self_iff_false, cast_eq, Fin.val_one, Nat.one_lt_ofNat, Fin.val_two, Nat.lt_succ_self,
      show (3 : Fin 4).1 = 3 by rfl, realize_rel, and_imp]
    rintro rfl rfl h
    convert h using 1
    ext i
    fin_cases i <;> rfl
  · simp only [Set.mem_singleton_iff, Equality.Axiom4] at ax4
    intros _ inst v xs
    subst φ
    intros x y z w
    simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_imp, realize_inf,
      realize_bdEqual, Term.realize_var, Sum.elim_inr, Fin.snoc, Fin.val_zero, Nat.ofNat_pos,
      ↓reduceDIte, Fin.castSucc_castLT, Fin.coe_castLT, zero_lt_one, Nat.zero_eq, Fin.coe_fin_one,
      lt_self_iff_false, cast_eq, Fin.val_one, Nat.one_lt_ofNat, Fin.val_two, Nat.lt_succ_self,
      show (3 : Fin 4).1 = 3 by rfl, Term.realize_func, and_imp]
    rintro rfl rfl
    congr
    ext i
    fin_cases i <;> rfl

lemma spec (φ : Lang.BoundedFormula α (n +1)) (h : ⊧ φ) : ⊧ ∃'φ := by
  intros S inst _ _
  simp_all
  rcases inst with ⟨_, _, _, _⟩
  exact (exists_const S).mpr trivial

lemma mp (φ ψ : Lang.BoundedFormula α n) (h1 : ⊧ (ψ ⟹ φ)) (h2 : ⊧ ψ) : ⊧ φ := by
  intros S inst v xs
  specialize h1 S v xs; specialize h2 S v xs
  simp_all

lemma subst (φ : Lang.BoundedFormula α n) (f : α → Lang.Term β) (h : ⊧ φ) : ⊧ φ.subst f := by
  intros S inst v xs
  simp_all

lemma exists_intro (φ : Lang.BoundedFormula α (n + 1)) (ψ : Lang.BoundedFormula α n)
    (h : ⊧ (φ ⟹ ψ.liftAt 1 n)) : ⊧ ∃'φ ⟹ ψ := by
  intros S inst v xs
  simp_all only [realize_imp, realize_ex, Nat.succ_eq_add_one, forall_exists_index]
  intro x hφ
  specialize h S v (Fin.snoc xs x)
  simp_all only [realize_imp, le_refl, realize_liftAt, Fin.is_lt, Fin.addNat_one, ite_true,
    true_implies]
  convert h using 1
  change xs = Fin.snoc xs x ∘ fun i => Fin.castSucc i
  simp [Fin.snoc_castSucc]

end soundness

lemma soundness (φ : Lang.BoundedFormula α n) (h : ⊢ φ) : ⊧ φ := by
  induction h with
| hyp h => simp_all
| ax h => exact soundness.ax h
| induc h => exact soundness.induc h
| bool h => exact soundness.bool h
| eq h => exact soundness.eq h
| spec φ _ h => exact soundness.spec φ h
| mp φ ψ _ _ h1 h2 => exact soundness.mp φ ψ h1 h2
| subst φ f _ h => exact soundness.subst φ f h
| exists_intro φ ψ _ h => exact soundness.exists_intro φ ψ h

theorem completeness (φ : Lang.BoundedFormula α n) : ⊢ φ ↔ ⊧ φ := by
  refine ⟨soundness φ, ?_⟩
  sorry

lemma prf_iff_prf_of_prf_iff (φ ψ : Lang.BoundedFormula α n) (iff: ⊢ φ ⇔ ψ) : (⊢ φ ↔ ⊢ ψ) := by
  constructor
  <;> intro prf
  <;> rw [completeness] at *
  <;> intros S _ v xs
  <;> specialize iff S v xs
  <;> specialize prf S v xs
  <;> simp_all

lemma prf_neg_iff_of_prf_iff (φ ψ : Lang.BoundedFormula α n) (iff: ⊢ φ ⇔ ψ) : ⊢ ∼φ ⇔ ∼ψ := by
  rw [completeness] at *
  intros S _ v xs
  specialize iff S v xs
  simp_all

lemma prf_of_prf_neg_neg (φ : Lang.BoundedFormula α n) (h : ⊢ ∼(∼φ)) : ⊢ φ := by
  rw [completeness] at *
  intros S _ v xs
  specialize h S v xs
  simp_all

lemma models_iff_of_prf_iff (S : Type) [Model S] (φ ψ : Lang.BoundedFormula α n) (h : ⊢ φ ⇔ ψ) :
    S ⊧ φ ↔ S ⊧ ψ := by
  rw [completeness] at h
  specialize h S
  simp [models] at *
  aesop

end HF
