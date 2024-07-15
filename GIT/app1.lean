import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

open FirstOrder Language BoundedFormula

/-!
# Appendix 1: Axioms and basic results of hereditarily finite set theory

In this file, Appendix 1 of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness Theorems' is formalised.
It presents the language, axioms and basic results of hereditarily finite set theory.

## Main results

- `exten_prop`: Extensionality property.
- `exists_union`: Existence of the union of two sets.
- `exists_union_set`: Existence of the union of a set of sets.
- `comp_scheme`: Comprehension scheme.
- `repl_scheme`: Replacement scheme.
- `exists_power`: Existence of the power set.
- `found_prop`: Foundation property.

## Notation

- `◁` : enlarging, see `HF.enlarge`.

## References

S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.
-/

/-- The first-order language of HF. -/
def HFLang : Language.{0, 0} where
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
abbrev HFLang.emptySetSymbol : HFLang.Functions 0 := PUnit.unit

local notation "∅'" => HFLang.emptySetSymbol

/-- Enlargement: 2-ary function symbol. -/
abbrev HFLang.enlargementSymbol : HFLang.Functions 2 := PUnit.unit

local notation "◁'" => HFLang.enlargementSymbol

/-- Membership: 2-ary relation symbol. -/
abbrev HFLang.membershipSymbol : HFLang.Relations 2 := PUnit.unit

local notation t " ∈' " s => HFLang.membershipSymbol.boundedFormula ![t, s]

universe u

/-- HF class -/
class HFPrior (s : Type u) where
  /-- Empty set: constant symbol. -/
  EmptySet : s
  /-- Enlargement: 2-ary function symbol. -/
  Enlarging : s → s → s
  /-- Membership: 2-ary relation symbol. -/
  Mem : s → s → Prop

/-- Write `∅` instead of `empty`. -/
instance (s) [HFPrior s] : EmptyCollection s := ⟨HFPrior.EmptySet⟩

/-- Write `∈` instead of `mem`. -/
instance (s) [HFPrior s] : Membership s s := ⟨HFPrior.Mem⟩

/-- Write `◁` instead of `enlarge`. -/
infixl:90 " ◁ " => HFPrior.Enlarging

@[simps]
instance (s) [HFPrior s] : HFLang.Structure s where
  funMap {n} _ h := match n with
  | 0 => ∅
  | 2 => h 0 ◁ h 1
  RelMap {n} _ h := match n with
  | 2 => h 0 ∈ h 1

/-- HF axioms -/
class HF (s : Type u) extends HFPrior s where
  /-- Axiom 1 "for the empty set". -/
  empty (z : s) : z = ∅ ↔ ∀ x, x ∉ z
  /-- Axiom 2 "for enlargement". -/
  enlarge (x y z : s) : z = x ◁ y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y
  /-- Axiom 3: the induction principle. The addtional four goals (next to base and step)
  ensure induction is over all formulae rather than over all predicates.  -/
  induction (α : s → Prop) (base : α ∅) (step : ∀ x y, α x → α y → α (x ◁ y)) (z : s)
      (n : Nat) (f : Language.BoundedFormula HFLang (Fin n) 1) (t : (Fin n) → s)
      (hP : α z ↔ f.Realize t (fun _ ↦ z)) : α z

attribute [elab_as_elim] HF.induction

suppress_compilation

variable {S : Type u} [HF S]

namespace HF

lemma set_notin_empty (x : S) : x ∉ (∅ : S) := by revert x; rw [← HF.empty ∅]

@[simp] lemma set_in_empty_iff_false (x : S) : x ∈ (∅ : S) ↔ False := by
  refine ⟨by exact set_notin_empty x, by simp⟩

@[simp] lemma enlarge_iff (u x y : S) : u ∈ x ◁ y ↔ u ∈ x ∨ u = y := by
  have := HF.enlarge x y (x ◁ y); simp_all only [true_iff]

lemma enlarge_empty (z y : S) : z ∈ ∅ ◁ y ↔ z = y := by simp

theorem exten_prop (z : S) (x : S) : x = z ↔ ∀ u, u ∈ x ↔ u ∈ z := by
  induction' x using HF.induction with x y _ _
  · simp_rw [set_notin_empty, false_iff]
    refine ⟨by intro h; rw [← h]; simp [set_notin_empty], ?_⟩
    rw [← HF.empty]
    exact fun a ↦ id (Eq.symm a)
  · refine ⟨by intro h; rw [h]; simp, ?_⟩
    have := HF.enlarge x y z; intro _
    simp_all only [enlarge_iff, implies_true, iff_true]
  · exact 1
  · exact (&0 =' .var (.inl 0)) ⇔ ∀' ((&1 ∈' &0) ⇔ (&1 ∈' .var (.inl 0)))
  · exact z
  · simp; rfl

/-- Singleton — notation in paper: {x}. -/
abbrev Single (x : S) : S := ∅ ◁ x

/-- Pair — notation in paper: {x, y}. -/
abbrev Pair (x y : S) : S := (Single x) ◁ y

/-- Ordered pair — notation in paper: ⟨x,y⟩ = {{x},{x,y}}. -/
abbrev OrdPair (x y : S) : S := Pair (Single x) (Pair x y)

lemma single_iff (u x : S) : u ∈ Single x ↔ u = x := by exact enlarge_empty u x

lemma pair_iff (u x y : S) : u ∈ Pair x y ↔ u = x ∨ u = y := by simp

lemma duplic_pair_eq_single (x : S) : Pair x x = Single x := by
  rw [exten_prop]; simp

@[simp] lemma single_eq_iff_eq (x y : S) : Single x = Single y ↔ x = y := by
  rw [exten_prop]; simp

@[simp] lemma pair_eq_single_iff (x y z : S) : (Pair y z = Single x) ↔ (x = y ∧ x = z) := by
  refine ⟨?_, by intro h; cases' h with h1 h2; rw [← h1, ← h2]; exact duplic_pair_eq_single x⟩
  intro h; rw [exten_prop] at h
  simp only [enlarge_iff, set_in_empty_iff_false, false_or] at h
  have h' := h; specialize h y; specialize h' z
  simp_all

@[simp] lemma single_eq_pair_iff (x y z : S) : (Single x = Pair y z) ↔ (x = y ∧ x = z) := by
  rw [eq_comm]; simp

lemma pair_equal (x y u v : S) (h : Pair x y = Pair u v) : (x ∈ Pair u v ∧ y ∈ Pair u v) := by
  simp_rw [exten_prop, pair_iff] at h
  simp only [enlarge_iff, set_in_empty_iff_false, false_or]
  refine ⟨by specialize h x; simp_all, by specialize h y; simp_all⟩

@[simp] lemma ordPair_equal (x y u v : S) : OrdPair x y = OrdPair u v ↔ x = u ∧ y = v := by
  refine ⟨?_, by simp_all⟩
  intro h; have h' := h; rw [eq_comm] at h'
  apply pair_equal at h; cases' h with h1 h2
  apply pair_equal at h'; cases' h' with h1' h2'
  simp only [enlarge_iff, set_in_empty_iff_false, single_eq_iff_eq, pair_eq_single_iff, single_eq_pair_iff, false_or] at *
  cases' h1' with u_eq_x h1'
  · cases' h2' with h2' h2'
    · cases' h2' with x_eq_u x_eq_v
      simp_rw [← x_eq_u, ← x_eq_v, duplic_pair_eq_single, pair_eq_single_iff, true_and, or_self] at h2
      subst x_eq_u x_eq_v h2; simp_all
    · apply pair_equal at h2'; simp_rw [u_eq_x, pair_iff, true_or, true_and] at h2'
      cases' h2' with v_eq_x v_eq_y
      · simp_rw [u_eq_x, v_eq_x, duplic_pair_eq_single, pair_eq_single_iff, true_and, or_self] at h2
        subst v_eq_x h2 u_eq_x; simp_all
      · simp_all
  · cases' h1' with u_eq_x u_eq_y
    rw [← u_eq_x, ← u_eq_y, duplic_pair_eq_single, pair_eq_single_iff] at h2'; simp_all

theorem exists_union (x y : S) : ∃(z : S), ∀(u : S), (u ∈ z ↔ (u ∈ x ∨ u ∈ y))  := by
  induction' x using HF.induction with x w hx _
  · use y; simp
  · cases' hx with xUy hxUy
    use xUy ◁ w
    simp only [enlarge_iff, hxUy]; tauto
  · exact 1
  · exact ∃' ∀' ((&2 ∈' &1) ⇔ ((&2 ∈' &0) ⊔ (&2 ∈' .var (.inl 0))))
  · exact y
  · simp; rfl

/-- x ∪ y -/
def Union (x y : S) : S := (exists_union x y).choose

@[simp] lemma union_iff (x y : S) : ∀ (u : S), u ∈ Union x y ↔ u ∈ x ∨ u ∈ y :=
  (exists_union x y).choose_spec

-- Theorem 1.6 (Existence of the union of a set of sets)

theorem exists_unionSet (x : S) : ∃(z : S), ∀(u : S), (u ∈ z ↔ (∃ y ∈ x, u ∈ y))  := by
  induction' x using HF.induction with x w hx _
  · use ∅; simp
  · cases' hx with Ux hUx
    use Union Ux w
    simp_all only [enlarge_iff, or_and_right, exists_or, exists_eq_left, union_iff, implies_true]
  · exact 0
  · exact ∃' ∀' ((&2 ∈' &1) ⇔ (∃' ((&3 ∈' &0) ⊓ (&2 ∈' &3))))
  · rename_i a; exact Fin.elim0 a
  · simp; rfl

/-- ⋃ x -/
def UnionSet (x : S) : S := (exists_unionSet x).choose

lemma unionSet_iff (x : S) : ∀(u : S), (u ∈ UnionSet x ↔ (∃ y ∈ x, u ∈ y)) :=
  (exists_unionSet x).choose_spec


-- Theorem 1.7 (Comprehension Scheme)

theorem comp_scheme (x : S) (φ : S → Prop) : ∃ (z : S), ∀ (u : S), (u ∈ z ↔ u ∈ x ∧ φ u) := by sorry
  -- revert x -- to prove ∀x α(x) using HF3/induction
  -- apply HF.induction
  -- -- base case
  -- · use ∅  -- take z = ∅
  --   simp [set_notin_empty]
  -- -- inductive step
  -- · intros x y hx _
  --   simp_rw [enlarge_iff]
  --   cases' hx with xφ hxφ  -- xφ is {u ∈ x : φ(u)} , which exists by hypothesis
  --   by_cases hφy : φ y
  --   · use xφ ◁ y  -- take z = {u ∈ x : φ(u)} ◁ y
  --     simp_rw [enlarge_iff]; aesop
  --   · use xφ; aesop  -- take z = {u ∈ x : φ(u)}

/-- {u ∈ x : φ(u)} -/
noncomputable def pred_set (x : S) (φ : S → Prop) : S := (comp_scheme x φ).choose

lemma pred_set_iff (x : S) (φ : S → Prop) : ∀ (u : S), (u ∈ pred_set x φ ↔ u ∈ x ∧ φ u) :=
  (comp_scheme x φ).choose_spec


-- Definition 1.8 (Intersection)

/-- x ∩ y = {u ∈ x : u ∈ y} -/
noncomputable def inter (x : S) (y : S) : S := pred_set x (fun u ↦ u ∈ y)

lemma inter_iff (x y : S) : ∀ (u : S), (u ∈ inter x y ↔ u ∈ x ∧ u ∈ y) := by
  exact pred_set_iff _ _

/-- ⋂ x = {u ∈ ⋃ x : ∀ v ∈ x, u ∈ v} -/
noncomputable def inter_set (x : S) : S := pred_set (UnionSet x) (fun u ↦ ∀ v ∈ x, u ∈ v)

lemma inter_set_iff (x : S) :
    ∀ (u : S), (u ∈ inter_set x ↔ u ∈ UnionSet x ∧ ∀ v ∈ x, u ∈ v) := by
  exact pred_set_iff _ _

lemma inter_enlarge (x y : S) : inter (x ◁ y) x = x := by
  simp_rw [exten_prop, inter_iff, enlarge_iff]; aesop


-- Theorem 1.9 (Replacement Scheme)

theorem repl_scheme (x : S) (ψ : S → S → Prop) :
    (∀ u ∈ x, ∃! v, ψ u v) → (∃ (z : S), ∀ v, (v ∈ z ↔ ∃ u ∈ x, ψ u v)) := by sorry
  -- revert x -- to prove ∀x α(x) using HF3/induction
  -- apply HF.induction
  -- -- base case
  -- · intro _; use ∅  -- take z = ∅
  --   simp [set_notin_empty]
  -- -- inductive step
  -- · intros x y hx _ h
  --   simp_rw [enlarge_iff] at h; have h2 := h
  --   specialize h y; simp only [or_true, forall_true_left] at h
  --   cases' h with vy hvy
  --   have hx1 : (∀ u ∈ x, ∃! v, ψ u v) := by simp_all
  --   specialize hx hx1
  --   cases' hx with xψ hxψ  -- xψ is {v : ∃ u ∈ x, ψ(u,v)}, which exists by hypothesis
  --   use xψ ◁ vy  -- take z = {v : ∃ u ∈ x, ψ(u,v)} ◁ vy
  --   simp_rw [enlarge_iff]; aesop

/-- {v : ∃ u ∈ x, ψ(u,v)} -/
noncomputable def repl (x : S) (ψ : S → S → Prop) (h : (∀ u ∈ x, ∃! v, ψ u v)) : S
    := (repl_scheme x ψ h).choose

lemma repl_iff (x : S) (ψ : S → S → Prop) (h : (∀ u ∈ x, ∃! v, ψ u v)) :
    ∀ (v : S), (v ∈ repl x ψ h ↔ ∃ u ∈ x, ψ u v) := (repl_scheme x ψ h).choose_spec


-- Definition 1.10 (Subset relation)

/-- y ⊆ x -/
abbrev subset_eq (y x : S) : Prop := ∀ (v : S), v ∈ y → v ∈ x

/-- y ⊂ x -/
abbrev subset (y x : S) : Prop := subset_eq y x ∧ y ≠ x


-- Theorem 1.11 (Existence of the power set)

lemma subset_enlarge (u x y Px : S) (hPx : ∀ (u : S), u ∈ Px ↔ subset_eq u x) :
    subset_eq u (x ◁ y) ↔ (u ∈ Px) ∨ (∃ v ∈ Px, u = v ◁ y) := by
  constructor
  · intro hu
    simp_rw [subset_eq, enlarge_iff] at hu
    by_cases hy : y ∈ u
    · right
      use inter u x; constructor  -- the required v is u ∩ x
      · simp_rw [hPx, subset_eq, inter_iff]; simp_all
      · simp_rw [HF.enlarge, inter_iff]; aesop
    · left; rw [hPx, subset_eq]
      intros v hv; specialize hu v hv; aesop
  · intro hu; cases' hu with hul hur
    · rw [hPx, subset_eq] at hul
      simp_rw [subset_eq, enlarge_iff]; simp_all
    · cases' hur with v hv
      cases' hv with hv1 hv2; rw [HF.enlarge] at hv2
      simp_rw [subset_eq, enlarge_iff, hv2]; aesop

theorem exists_power (x : S) : ∃ (z : S), ∀ (u : S), u ∈ z ↔ subset_eq u x := by
  induction' x using HF.induction with x y hx _
  · sorry
  · sorry
  · exact 0
  · exact ∃' ∀' ((&2 ∈' &1) ⇔ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &0))))
  · rename_i a; exact Fin.elim0 a
  · simp; rfl
  -- revert x -- to prove ∀x α(x) using HF3/induction
  -- apply HF.induction
  -- -- base case
  -- · use single ∅  -- take z = {∅}
  --   simp_rw [single_iff, subset_eq, exten_prop]
  --   simp [set_notin_empty]
  -- -- inductive step
  -- · intros x y hx _
  --   cases' hx with Px hPx  -- Px is the power set P(x), which exists by hypothesis
  --   have h : (∀ v ∈ Px, ∃! u, u = v ◁ y) := by  -- condition for usage replacement scheme
  --     intros v _; use v ◁ y; simp_all
  --   -- take z = P(x) ∪ {u : ∃ v ∈ P(x), u = v ◁ y}
  --   use union (Px) (repl (Px) (fun v u ↦ u = v ◁ y) (h))
  --   intro u; have hsub := subset_enlarge u x y Px  -- use the lemma
  --   specialize hsub hPx; rw [hsub, union_iff, repl_iff]

  /-- Power set: P(x) -/
noncomputable def power (x : S) : S := (exists_power x).choose

lemma power_iff (x : S) : ∀ (u : S), u ∈ power x ↔ subset_eq u x :=
  (exists_power x).choose_spec


-- Definition 1.12 (∈-minimal element)

/-- w an ∈-minimal element of z: w ∈ z ∧ w ∩ z = ∅ -/
abbrev mem_min (w z : S) : Prop := w ∈ z ∧ inter w z = ∅


-- Theorem 1.13 (Foundation Property)

lemma found_prop_lemma (z : S) : (∀ w ∈ z, inter w z ≠ ∅) → ∀ x, x ∉ z ∧ inter x z = ∅ := by sorry
  -- intro h; apply HF.induction
  -- -- base case
  -- · constructor
  --   · by_contra hn
  --     specialize h ∅ hn; simp only [ne_eq] at h
  --     simp_rw [exten_prop, inter_iff] at h; simp_all [set_notin_empty]
  --   · simp_rw [exten_prop, inter_iff]; simp_all [set_notin_empty]
  -- -- inductive step
  -- · intros x y hx hy
  --   by_contra hn; rw [not_and_or] at hn
  --   simp only [not_not] at hn
  --   have hxyz : (¬inter (x ◁ y) z = ∅) → False := by  -- covers both Case 1 and Case 2
  --     intro hne; have hstep : inter x z ≠ ∅ → False := by simp_all
  --     apply hstep
  --     simp_rw [exten_prop, inter_iff, enlarge_iff] at hne; simp only [not_forall] at hne
  --     cases' hne with w hw; simp [set_notin_empty] at hw
  --     cases' hw with hw1 hw2; cases' hw1 with hwl hwr
  --     · simp_rw [exten_prop, inter_iff] at hx; simp_all [set_notin_empty]
  --     · simp_rw [exten_prop, inter_iff] at hy; simp_all
  --   cases' hn with hnl hnr  -- Case 1 and Case 2
  --   · specialize h (x ◁ y) hnl; simp only [ne_eq] at h ; simp_all
  --   · simp_all

theorem found_prop (z : S) : z ≠ ∅ → ∃ w, mem_min w z := by
  have h := found_prop_lemma z
  rw [not_imp_comm, not_exists]; intro h2
  simp_rw [mem_min] at h2; simp only [not_and] at h2
  simp only [ne_eq] at h
  specialize h h2; rw [exten_prop]
  simp_all [set_notin_empty]


-- Corollary 1.14

theorem set_notin_set (x : S) : x ∉ x := by
  have h := found_prop (Single x)
  have hx : Single x ≠ ∅ := by
    simp only [ne_eq]; simp_rw [Single, exten_prop, enlarge_iff]
    simp_all [set_notin_empty]
  specialize h hx
  cases' h with w hw; rw [mem_min] at hw
  simp_rw [Single, exten_prop, inter_iff, enlarge_iff] at hw
  simp only [set_notin_empty] at hw; aesop

end HF
