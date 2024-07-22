import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import GIT.FirstOrder_reverse

open FirstOrder Language BoundedFormula

/-!
# Appendix 1: Axioms and basic results of hereditarily finite set theory

In this file, Appendix 1 of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness Theorems' is formalised.
It presents the language, axioms and basic results of hereditarily finite set theory.

## Main results

- `exten_prop`: Extensionality property.
- `exists_union`: Existence of the union of two sets.
- `exists_unionOfSet`: Existence of the union of a set of sets.
- `comp_scheme`: Comprehension scheme.
- `repl_scheme`: Replacement scheme.
- `exists_powerSet`: Existence of the power set.
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

local notation " ◁' " => HFLang.enlargementSymbol

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

/-- Write `∅` instead of `EmptySet`. -/
instance (s) [HFPrior s] : EmptyCollection s := ⟨HFPrior.EmptySet⟩

/-- Write `∈` instead of `Mem`. -/
instance (s) [HFPrior s] : Membership s s := ⟨HFPrior.Mem⟩

/-- Write `◁` instead of `Enlarging`. -/
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
  ensure induction is over all formulae in the first-order language of HF rather than over all predicates.  -/
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

theorem exists_unionOfSet (x : S) : ∃(z : S), ∀(u : S), (u ∈ z ↔ (∃ y ∈ x, u ∈ y))  := by
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
def UnionOfSet (x : S) : S := (exists_unionOfSet x).choose

@[simp] lemma unionOfSet_iff (x : S) : ∀ (u : S), (u ∈ UnionOfSet x ↔ (∃ y ∈ x, u ∈ y)) :=
  (exists_unionOfSet x).choose_spec

theorem comp_scheme (x : S) (φ : S → Prop) {n} (f : BoundedFormula HFLang (Fin n) 1) (c : Fin n → S)
    (hφ : ∀ x, φ x ↔ f.Realize c ![x]) : ∃ (z : S), ∀ (u : S), (u ∈ z ↔ u ∈ x ∧ φ u) := by
  induction' x using HF.induction with x y hx _
  · use ∅; simp
  · simp only [enlarge_iff]
    cases' hx with xφ hxφ
    if φ y then use xφ ◁ y; simp only [enlarge_iff]; aesop
    else use xφ; aesop
  · exact n
  · exact ∃' ∀' ((&2 ∈' &1) ⇔ ((&2 ∈' &0) ⊓ (f.liftAt 2 0)))
  · rename_i a; exact c a
  · simp
    convert Iff.rfl
    rw [realize_liftAt (by norm_num), hφ]
    convert Iff.rfl
    simp_all only [Nat.reduceAdd, Fin.coe_fin_one, lt_self_iff_false, ↓reduceIte]
    ext1 x_2
    simp_all only [Matrix.cons_val_fin_one, Function.comp_apply]
    rfl

/-- Any definable (defined through a formula φ) sublass of a set x is a set — {u ∈ x : φ(u)} -/
def SetByFormula (x : S) (φ : S → Prop) {n} (f : BoundedFormula HFLang (Fin n) 1) (c : Fin n → S)
    (hφ : ∀ x, φ x ↔ f.Realize c ![x]) : S := (comp_scheme x φ f c hφ).choose

@[simp] lemma setByFormula_iff (x : S) (φ : S → Prop) {n} (f : BoundedFormula HFLang (Fin n) 1) (c : Fin n → S)
    (hφ : ∀ x, φ x ↔ f.Realize c ![x]) : ∀ (u : S), (u ∈ SetByFormula x φ f c hφ ↔ u ∈ x ∧ φ u) :=
  (comp_scheme x φ f c hφ).choose_spec

/-- x ∩ y = {u ∈ x : u ∈ y} -/
def Inter (x : S) (y : S) : S :=
    SetByFormula (n := 1) x (fun z ↦ z ∈ y)
      ((&0 ∈' .var (.inl 0))) (![y]) (by simp)

@[simp] lemma inter_iff (x y : S) : ∀ (u : S), (u ∈ Inter x y ↔ u ∈ x ∧ u ∈ y) :=
  setByFormula_iff _ _ _ _ _

/-- ⋂ x = {u ∈ ⋃ x : ∀ v ∈ x, u ∈ v} -/
def InterSet (x : S) : S :=
  SetByFormula (n := 1) (UnionOfSet x) (fun u ↦ ∀ v ∈ x, u ∈ v)
      (∀' ((&1 ∈' .var (.inl 0)) ⟹ (&0 ∈' &1))) ![x] (by simp [Fin.snoc])


@[simp] lemma inter_set_iff (x : S) :
    ∀ (u : S), (u ∈ InterSet x ↔ u ∈ UnionOfSet x ∧ ∀ v ∈ x, u ∈ v) :=
  setByFormula_iff _ _ _ _ _

lemma inter_enlarge (x y : S) : Inter (x ◁ y) x = x := by
  simp only [exten_prop, inter_iff, enlarge_iff, and_iff_right_iff_imp]
  intro u a
  simp_all only [true_or]

theorem repl_scheme (x : S) {n} (ψ : S → S → Prop)
    (f : BoundedFormula HFLang (Fin n) 2)  (qf : f.IsQF)
    (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) :
    (∀ u ∈ x, ∃ v, (ψ u v ∧ ∀ w, (ψ u w → w = v))) → (∃ (z : S), ∀ v, (v ∈ z ↔ ∃ u ∈ x, ψ u v)) := by
  induction' x using HF.induction with x y hx _
  · intro _; use ∅; simp
  · simp only [enlarge_iff]; intro h
    have : (∀ u ∈ x, ∃ v, ψ u v ∧ ∀ (w : S), ψ u w → w = v) := by intro u a_1; simp_all only [true_or]
    specialize hx this
    cases' hx with xψ hxψ
    specialize h y
    simp only [or_true, true_implies] at h
    rcases h with ⟨vy, ⟨ψvy, vy_uniq⟩⟩
    use xψ ◁ vy; simp only [enlarge_iff, hxψ]
    intro v
    constructor
    · intro h; cases' h with h1 h2
      · cases' h1 with u hu; use u; simp_all only [true_or, and_self]
      · use y; simp_all only [or_true, and_self]
    · intro h; rcases h with ⟨u, ⟨hu ,ψuv⟩⟩
      cases' hu with u_in_x u_eq_y
      · left; use u
      · right; subst u; exact vy_uniq v ψuv
  · exact n
  · exact
      (∀' ((&1 ∈' &0) ⟹ ∃' (f.liftAt 1 0 ⊓ ∀' ((f.liftAt 1 0).liftAt 1 2 ⟹ &3 =' &2))))
    ⟹ ∃' ∀' ((&2 ∈' &1) ⇔ ∃' ((&3 ∈' &0) ⊓ f.reverse.liftAt 2 0))
  · rename_i a; exact c a
  · simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_imp, realize_all,
    Nat.succ_eq_add_one, realize_rel, instStructureHFLangOfHFPrior_RelMap, Matrix.cons_val_zero,
    Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons, realize_ex, realize_inf,
    realize_bdEqual, realize_iff]
    convert Iff.rfl
    · rw [realize_liftAt (by norm_num), hψ]
      convert Iff.rfl using 1
      congr! 1
      ext i
      fin_cases i <;> simp <;> rfl
    · rw [realize_liftAt (by norm_num), realize_liftAt (by norm_num), hψ]
      convert Iff.rfl using 1
      congr! 1
      ext i
      fin_cases i <;> simp <;> rfl
    · rw [realize_liftAt (by norm_num), realize_reverse_of_isQF (hφ := qf), hψ]
      rename_i _ a b c
      convert Iff.rfl using 1
      congr! 1
      ext i
      fin_cases i <;> simp <;> rfl

/-- The image of any set x under any definable mapping ψ is a set – {v : ∃ u ∈ x, ψ(u,v)} -/
def SetByImage (x : S) {n} (ψ : S → S → Prop)
    (f : BoundedFormula HFLang (Fin n) 2)  (qf : f.IsQF)
    (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) (h : (∀ u ∈ x, ∃! v, ψ u v)) : S
    := (repl_scheme x ψ f qf c hψ h).choose

@[simp] lemma setByImage_iff (x : S) {n} (ψ : S → S → Prop)
    (f : BoundedFormula HFLang (Fin n) 2)  (qf : f.IsQF)
    (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) (h : (∀ u ∈ x, ∃! v, ψ u v)) :
    ∀ (v : S), (v ∈ SetByImage x ψ f qf c hψ h ↔ ∃ u ∈ x, ψ u v) := (repl_scheme x ψ f qf c hψ h).choose_spec

/-- y ⊆ x -/
abbrev SubsetEq (y x : S) : Prop := ∀ (v : S), v ∈ y → v ∈ x

/-- y ⊂ x -/
abbrev Subset (y x : S) : Prop := SubsetEq y x ∧ y ≠ x

lemma exists_powerSet_aux (u x y Px : S) (hPx : ∀ (u : S), u ∈ Px ↔ SubsetEq u x) :
    SubsetEq u (x ◁ y) ↔ (u ∈ Px) ∨ (∃ v ∈ Px, u = v ◁ y) := by
  simp_rw [SubsetEq] at *
  refine ⟨?_, by aesop⟩
  intro hu; simp only [enlarge_iff] at hu
  by_cases y_in_u : y ∈ u
  · right; use Inter u x
    refine ⟨by simp_all, by simp only [enlarge, inter_iff]; aesop⟩
  · left; rw [hPx]
    intros v hv; specialize hu v hv; aesop

theorem exists_powerSet (x : S) : ∃ (z : S), ∀ (u : S), u ∈ z ↔ SubsetEq u x := by
  induction' x using HF.induction with x y hx _
  · use Single ∅
    simp [SubsetEq, exten_prop]
  · cases' hx with Px hPx
    have : (∀ v ∈ Px, ∃! u, u = v ◁ y) := by intros v _; use v ◁ y; simp_all
    let z := SetByImage (n := 1) Px (fun v u ↦ u = v ◁ y) (&1 =' (.func ◁' ![&0, .var (.inl 0)]))
        (by refine IsAtomic.isQF ?_; exact IsAtomic.equal ((var ∘ Sum.inr) 1) (func ◁' ![(var ∘ Sum.inr) 0, var (Sum.inl 0)]))
        (![y]) (by simp) this
    use Union Px z
    intro u
    rw [exists_powerSet_aux u x y Px hPx, union_iff, setByImage_iff]
  · exact 0
  · exact ∃' ∀' ((&2 ∈' &1) ⇔ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &0))))
  · rename_i a; exact Fin.elim0 a
  · simp; rfl

  /-- Power set -/
def PowerSet (x : S) : S := (exists_powerSet x).choose

lemma powerSet_iff (x : S) : ∀ (u : S), u ∈ PowerSet x ↔ SubsetEq u x :=
  (exists_powerSet x).choose_spec

lemma found_prop_aux (z : S) : (∀ w ∈ z, Inter w z ≠ ∅) → ∀ x, x ∉ z ∧ Inter x z = ∅ := by sorry
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

theorem found_prop (z : S) : z ≠ ∅ → ∃ w, w ∈ z ∧ Inter w z = ∅ := by
  rw [not_imp_comm, not_exists, exten_prop]
  intro h; simp only [not_and] at h
  simp_all [found_prop_aux z h]

theorem set_notin_itself (x : S) : x ∉ x := by
  obtain ⟨w, hw⟩ := found_prop (Single x) (by simp_rw [ne_eq, exten_prop]; simp_all)
  simp_rw [exten_prop, inter_iff, single_iff, set_in_empty_iff_false] at hw
  aesop

@[simp] lemma set_in_itself_iff_false (x : S) : x ∈ x ↔ False := by
  refine ⟨set_notin_itself x, by simp only [false_implies]⟩

end HF
