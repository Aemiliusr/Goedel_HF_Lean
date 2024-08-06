import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import GIT.FirstOrder_reverse

open FirstOrder Language BoundedFormula Classical

/-!
# Appendix 1: Axioms and basic results of hereditarily finite set theory
# Appendix 2: Ordinals of hereditarily finite set theory

In this file, the appendices of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness Theorems'
are formalised. It presents a systematic development of the theory of hereditarily finite sets.

## Main results

- `HFSet.exten_prop`: Extensionality property.
- `HFSet.exists_union`: Existence of the union of two sets.
- `HFSet.exists_sUnion`: Existence of the union of a set of sets.
- `HFSet.comp_scheme`: Comprehension scheme.
- `HFSet.repl_scheme`: Replacement scheme.
- `HFSet.exists_powerset`: Existence of the power set.
- `HFSet.found_prop`: Foundation property.
- `HFSet.IsOrd.comparability`: Comparability of ordinals.

## Notation

- `◁` : enlarging, see `HFSet.enlarge`.

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
class HF (s : Type u) where
  /-- Empty set: constant symbol. -/
  EmptySet : s
  /-- Enlargement: 2-ary function symbol. -/
  Enlarging : s → s → s
  /-- Membership: 2-ary relation symbol. -/
  Mem : s → s → Prop

/-- Write `∅` instead of `EmptySet`. -/
instance (s) [HF s] : EmptyCollection s := ⟨HF.EmptySet⟩

/-- Write `∈` instead of `Mem`. -/
instance (s) [HF s] : Membership s s := ⟨HF.Mem⟩

/-- Write `◁` instead of `Enlarging`. -/
infixl:90 " ◁ " => HF.Enlarging

@[simps]
instance (s) [HF s] : HFLang.Structure s where
  funMap {n} _ h := match n with
  | 0 => ∅
  | 2 => h 0 ◁ h 1
  RelMap {n} _ h := match n with
  | 2 => h 0 ∈ h 1

/-- HF axioms -/
class HFSet (s : Type u) extends HF s where
  /-- Axiom 1 "for the empty set". -/
  empty (z : s) : z = ∅ ↔ ∀ x, x ∉ z
  /-- Axiom 2 "for enlargement". -/
  enlarge (x y z : s) : z = x ◁ y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y
  /-- Axiom 3: the induction principle. The addtional four goals (next to base and step)
  ensure induction is over all formulae in the first-order language of HF rather than over all
  predicates.  -/
  induction (α : s → Prop) (base : α ∅) (step : ∀ x y, α x → α y → α (x ◁ y)) (z : s)
      (n : Nat) (f : Language.BoundedFormula HFLang (Fin n) 1) (t : (Fin n) → s)
      (hP : α z ↔ f.Realize t (fun _ ↦ z)) : α z

attribute [elab_as_elim] HFSet.induction

suppress_compilation

variable {S : Type u} [HFSet S]

namespace HFSet

lemma notin_empty (x : S) : x ∉ (∅ : S) := by revert x; rw [← empty ∅]

@[simp] lemma in_empty_iff_false (x : S) : x ∈ (∅ : S) ↔ False := by
  refine ⟨by exact notin_empty x, by simp⟩

lemma ne_empty_iff_exists_mem (x : S) : x ≠ ∅ ↔ ∃ y, y ∈ x := by
  rw [ne_eq, empty]
  push_neg
  rfl

@[simp] lemma mem_enlarge (u x y : S) : u ∈ x ◁ y ↔ u ∈ x ∨ u = y := by
  have := enlarge x y (x ◁ y); simp_all only [true_iff]

lemma mem_enlarge_empty (z y : S) : z ∈ ∅ ◁ y ↔ z = y := by simp

theorem exten_prop (z : S) (x : S) : x = z ↔ ∀ u, u ∈ x ↔ u ∈ z := by
  induction x using induction with
  | base =>
    simp_rw [notin_empty, false_iff]
    refine ⟨by intro h; rw [← h]; simp [notin_empty], ?_⟩
    rw [← empty]
    exact fun a ↦ id (Eq.symm a)
  | step x y _ _ =>
    refine ⟨by intro h; rw [h]; simp, ?_⟩
    have := enlarge x y z; intro _
    simp_all only [mem_enlarge, implies_true, iff_true]
  | n => exact 1
  | f => exact (&0 =' .var (.inl 0)) ⇔ ∀' ((&1 ∈' &0) ⇔ (&1 ∈' .var (.inl 0)))
  | t => exact z
  | hP =>
    simp only [Fin.isValue, Function.comp_apply, Nat.reduceAdd, realize_iff, realize_bdEqual,
    Term.realize_var, Sum.elim_inr, Sum.elim_inl, realize_all, Nat.succ_eq_add_one, realize_rel,
    instStructureHFLangOfHF_RelMap, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rfl

instance insert : Insert S S := ⟨fun y x => x ◁ y⟩

instance singleton : Singleton S S := ⟨fun x => ∅ ◁ x⟩

@[simp] lemma mem_singleton (u x : S) : u ∈ ({x} : S) ↔ u = x := mem_enlarge_empty u x

@[simp] lemma mem_pair (u x y : S) : u ∈ ({x, y} : S) ↔ u = x ∨ u = y := by
  simp only [insert, mem_enlarge, mem_singleton]; tauto

lemma duplic_pair_eq_single (x : S) : ({x, x} : S) = {x} := by simp [exten_prop]

@[simp] lemma singleton_eq_iff_eq (x y : S) : ({x} : S) = {y} ↔ x = y := by
  rw [exten_prop]; simp

@[simp] lemma pair_eq_singleton_iff (x y z : S) : (({y, z} : S) = {x}) ↔ (x = y ∧ x = z) := by
  refine ⟨?_, by intro h; rcases h with ⟨h1, h2⟩; rw [← h1, ← h2]; exact duplic_pair_eq_single x⟩
  intro h; rw [exten_prop] at h
  have h' := h; specialize h y; specialize h' z
  simp_all

@[simp] lemma singleton_eq_pair_iff (x y z : S) : (({x} : S) = {y, z}) ↔ (x = y ∧ x = z) := by
  rw [eq_comm]; simp

lemma pair_inj_aux (x y u v : S) (h : ({x, y} : S) = {u, v}) :
    (x ∈ ({u, v} : S) ∧ y ∈ ({u, v} : S)) := by
  simp only [exten_prop, mem_pair] at h
  simp only [mem_pair]
  constructor
  · specialize h x; simp only [implies_true, true_or, true_iff] at h
    simp_all [exten_prop]
  · specialize h y; simp only [implies_true, or_true, true_iff] at h
    simp_all [exten_prop]

/-- Ordered pair — {{x},{x,y}}. -/
abbrev pair (x y : S) : S := {{x}, {x, y}}

@[simp] lemma pair_inj (x y u v : S) : pair x y = pair u v ↔ x = u ∧ y = v := by
  refine ⟨?_, by simp_all⟩
  intro h; have h' := h; rw [eq_comm] at h'
  apply pair_inj_aux at h; rcases h with ⟨h1, h2⟩
  apply pair_inj_aux at h'; rcases h' with ⟨h1', h2'⟩
  simp only [mem_pair, singleton_eq_iff_eq, singleton_eq_pair_iff, pair_eq_singleton_iff] at *
  rcases h1' with u_eq_x | h1'
  · rcases h2' with h2' | h2'
    · rcases h2' with ⟨x_eq_u, x_eq_v⟩
      simp only [← x_eq_u, true_and, ← x_eq_v, duplic_pair_eq_single, pair_eq_singleton_iff,
        or_self] at h2
      subst x_eq_u x_eq_v h2; simp_all
    · apply pair_inj_aux at h2'; simp_rw [u_eq_x, mem_pair, true_or, true_and] at h2'
      refine h2'.elim ?_ (by simp_all)
      intro v_eq_x
      simp only [u_eq_x, true_and, v_eq_x, duplic_pair_eq_single, pair_eq_singleton_iff,
        or_self] at h2
      subst v_eq_x h2 u_eq_x; simp_all
  · rcases h1' with ⟨u_eq_x, u_eq_y⟩
    rw [← u_eq_x, ← u_eq_y, duplic_pair_eq_single, pair_eq_singleton_iff] at h2'; simp_all

theorem exists_union (x y : S) : ∃(z : S), ∀(u : S), (u ∈ z ↔ (u ∈ x ∨ u ∈ y))  := by
  induction x using induction with
  | base => use y; simp
  | step x w hx _ =>
    rcases hx with ⟨xUy, hxUy⟩
    use xUy ◁ w
    simp only [mem_enlarge, hxUy]; tauto
  | n => exact 1
  | f => exact ∃' ∀' ((&2 ∈' &1) ⇔ ((&2 ∈' &0) ⊔ (&2 ∈' .var (.inl 0))))
  | t => exact y
  | hP => simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_ex,
    Nat.succ_eq_add_one, realize_all, realize_iff, realize_rel, instStructureHFLangOfHF_RelMap,
    Matrix.cons_val_zero, Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons,
    realize_sup, Sum.elim_inl]; rfl

/-- x ∪ y. Defined through z ∈ x ∪ y ↔ (z ∈ x ∨ z ∈ y). -/
def union (x y : S) : S := (exists_union x y).choose

/-- x ∪ y. Defined through z ∈ x ∪ y ↔ (z ∈ x ∨ z ∈ y). -/
instance : Union S := ⟨union⟩

@[simp] lemma mem_union (x y u : S) : u ∈ x ∪ y ↔ u ∈ x ∨ u ∈ y := by
  revert u
  exact (exists_union x y).choose_spec

theorem exists_sUnion (x : S) : ∃(z : S), ∀(u : S), (u ∈ z ↔ (∃ y ∈ x, u ∈ y))  := by
  induction x using induction with
  | base => use ∅; simp
  | step x w hx _ =>
    rcases hx with ⟨Ux, hUx⟩
    use Ux ∪ w
    simp_all only [mem_enlarge, or_and_right, exists_or, exists_eq_left, mem_union, implies_true]
  | n => exact 0
  | f => exact ∃' ∀' ((&2 ∈' &1) ⇔ (∃' ((&3 ∈' &0) ⊓ (&2 ∈' &3))))
  | t => rename_i a; exact Fin.elim0 a
  | hP => simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_ex,
    Nat.succ_eq_add_one, realize_all, realize_iff, realize_rel, instStructureHFLangOfHF_RelMap,
    Matrix.cons_val_zero, Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons,
    realize_inf]; rfl

/-- ⋃ x. Defined through z ∈ ⋃ x ↔ (∃ y ∈ x, z ∈ y). -/
def sUnion (x : S) : S := (exists_sUnion x).choose

/-- ⋃ x. Defined through z ∈ ⋃ x ↔ (∃ y ∈ x, z ∈ y). -/
prefix:110 "⋃₀" => sUnion

@[simp] lemma mem_sUnion (x u : S) : (u ∈ ⋃₀ x ↔ (∃ y ∈ x, u ∈ y)) := by
  revert u
  exact (exists_sUnion x).choose_spec

theorem comp_scheme (x : S) (φ : S → Prop) {n} (f : BoundedFormula HFLang (Fin n) 1)
    (c : Fin n → S) (hφ : ∀ x, φ x ↔ f.Realize c ![x]) :
    ∃ (z : S), ∀ (u : S), (u ∈ z ↔ u ∈ x ∧ φ u) := by
  induction x using induction with
  | base => use ∅; simp
  | step x y hx _ =>
    simp only [mem_enlarge]
    rcases hx with ⟨xφ, hxφ⟩
    if φ y then use xφ ◁ y; simp only [mem_enlarge]; aesop
    else use xφ; aesop
  | n => exact n
  | f => exact ∃' ∀' ((&2 ∈' &1) ⇔ ((&2 ∈' &0) ⊓ (f.liftAt 2 0)))
  | t => rename_i a; exact c a
  | hP =>
    simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_ex, Nat.succ_eq_add_one,
      realize_all, realize_iff, realize_rel, instStructureHFLangOfHF_RelMap, Matrix.cons_val_zero,
      Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons, realize_inf]
    convert Iff.rfl
    rw [realize_liftAt (by norm_num), hφ]
    convert Iff.rfl
    simp_all only [Nat.reduceAdd, Fin.coe_fin_one, lt_self_iff_false, ↓reduceIte]
    ext1 x_2
    simp_all only [Matrix.cons_val_fin_one, Function.comp_apply]
    rfl

/-- Any definable (defined through a formula φ) sublass of a set x is a set — {u ∈ x : φ(u)} -/
def setOfMem (x : S) (φ : S → Prop) {n} (f : BoundedFormula HFLang (Fin n) 1) (c : Fin n → S)
    (hφ : ∀ x, φ x ↔ f.Realize c ![x]) : S := (comp_scheme x φ f c hφ).choose

@[simp] lemma mem_setOfMem (x u : S) (φ : S → Prop) {n} (f : BoundedFormula HFLang (Fin n) 1)
    (c : Fin n → S) (hφ : ∀ x, φ x ↔ f.Realize c ![x]) :
    (u ∈ setOfMem x φ f c hφ ↔ u ∈ x ∧ φ u) := by
  revert u
  exact (comp_scheme x φ f c hφ).choose_spec

/-- x ∩ y = {u ∈ x : u ∈ y} -/
def inter (x : S) (y : S) : S :=
    setOfMem (n := 1) x (fun z ↦ z ∈ y)
      ((&0 ∈' .var (.inl 0))) (![y]) (by simp)

/-- x ∩ y = {u ∈ x : u ∈ y} -/
instance : Inter S := ⟨inter⟩

@[simp] lemma mem_inter (x y u : S) : (u ∈ x ∩ y ↔ u ∈ x ∧ u ∈ y) :=
  mem_setOfMem (n := 1) x u (fun z ↦ z ∈ y) ((&0 ∈' .var (.inl 0))) (![y]) (by simp)

/-- ⋂ x = {u ∈ ⋃ x : ∀ v ∈ x, u ∈ v} -/
def sInter (x : S) : S :=
  setOfMem (n := 1) (⋃₀ x) (fun u ↦ ∀ v ∈ x, u ∈ v)
      (∀' ((&1 ∈' .var (.inl 0)) ⟹ (&0 ∈' &1))) ![x] (by simp [Fin.snoc])

/-- ⋂ x = {u ∈ ⋃ x : ∀ v ∈ x, u ∈ v} -/
prefix:110 "⋂₀ " => sInter

@[simp] lemma mem_sInter (x u : S) :
    (u ∈ ⋂₀ x ↔ u ∈ ⋃₀ x ∧ ∀ v ∈ x, u ∈ v) :=
  mem_setOfMem (n := 1) (⋃₀ x) u (fun u ↦ ∀ v ∈ x, u ∈ v)
      (∀' ((&1 ∈' .var (.inl 0)) ⟹ (&0 ∈' &1))) ![x] (by simp [Fin.snoc])

lemma inter_enlarge (x y : S) : (x ◁ y) ∩ x = x := by
  simp only [exten_prop, mem_inter, mem_enlarge, and_iff_right_iff_imp]
  intro u a
  simp_all only [true_or]

theorem repl_scheme (x : S) {n} (ψ : S → S → Prop)
    (f : BoundedFormula HFLang (Fin n) 2)  (qf : f.IsQF)
    (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) :
    (∀ u ∈ x, ∃ v, (ψ u v ∧ ∀ w, (ψ u w → w = v))) → (∃ (z : S), ∀ v, (v ∈ z ↔ ∃ u ∈ x, ψ u v))
    := by
  induction x using induction with
  | base => intro _; use ∅; simp
  | step x y hx _ =>
    simp only [mem_enlarge]; intro h
    have : (∀ u ∈ x, ∃ v, ψ u v ∧ ∀ (w : S), ψ u w → w = v) := by
      intro u a_1; simp_all only [true_or]
    specialize hx this
    rcases hx with ⟨xψ, hxψ⟩
    specialize h y
    simp only [or_true, true_implies] at h
    rcases h with ⟨vy, ⟨ψvy, vy_uniq⟩⟩
    use xψ ◁ vy; simp only [mem_enlarge, hxψ]
    intro v
    constructor
    · intro h; rcases h with h1 | h2
      · rcases h1 with ⟨u, hu⟩; use u; simp_all only [true_or, and_self]
      · use y; simp_all only [or_true, and_self]
    · intro h; rcases h with ⟨u, ⟨hu ,ψuv⟩⟩
      refine hu.elim (by intro _; left; use u) (by intro _; right; subst u; exact vy_uniq v ψuv)
  | n => exact n
  | f => exact
      (∀' ((&1 ∈' &0) ⟹ ∃' (f.liftAt 1 0 ⊓ ∀' ((f.liftAt 1 0).liftAt 1 2 ⟹ &3 =' &2))))
    ⟹ ∃' ∀' ((&2 ∈' &1) ⇔ ∃' ((&3 ∈' &0) ⊓ f.reverse.liftAt 2 0))
  | t => rename_i a; exact c a
  | hP =>
    simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_imp, realize_all,
    Nat.succ_eq_add_one, realize_rel, instStructureHFLangOfHF_RelMap, Matrix.cons_val_zero,
    Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons, realize_ex, realize_inf,
    realize_bdEqual, realize_iff]
    convert Iff.rfl
    · rw [realize_liftAt (by norm_num), hψ]
      convert Iff.rfl using 1
      congr! 1
      ext i
      fin_cases i <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, not_lt_zero', ↓reduceIte, Fin.addNat_one, Function.comp_apply,
        Fin.succ_zero_eq_one] <;> rfl
    · rw [realize_liftAt (by norm_num), realize_liftAt (by norm_num), hψ]
      convert Iff.rfl using 1
      congr! 1
      ext i
      fin_cases i <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, Fin.addNat_one, not_lt_zero', ↓reduceIte, Function.comp_apply,
        Fin.succ_zero_eq_one, Fin.val_one, Nat.one_lt_ofNat] <;> rfl
    · rw [realize_liftAt (by norm_num), realize_reverse_of_isQF (hφ := qf), hψ]
      rename_i _ a b c
      convert Iff.rfl using 1
      congr! 1
      ext i
      fin_cases i <;> simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, not_lt_zero', ↓reduceIte, Function.comp_apply, Fin.rev_zero] <;> rfl

/-- The image of any set x under any definable mapping ψ is a set – {v : ∃ u ∈ x, ψ(u,v)} -/
def setOfImage (x : S) {n} (ψ : S → S → Prop)
    (f : BoundedFormula HFLang (Fin n) 2)  (qf : f.IsQF)
    (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) (h : (∀ u ∈ x, ∃! v, ψ u v)) : S
    := (repl_scheme x ψ f qf c hψ h).choose

@[simp] lemma mem_setOfImage (x v : S) {n} (ψ : S → S → Prop)
    (f : BoundedFormula HFLang (Fin n) 2)  (qf : f.IsQF)
    (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) (h : (∀ u ∈ x, ∃! v, ψ u v)) :
    (v ∈ setOfImage x ψ f qf c hψ h ↔ ∃ u ∈ x, ψ u v) := by
  revert v
  exact (repl_scheme x ψ f qf c hψ h).choose_spec

/-- y ⊆ x -/
abbrev Subset (x y : S) : Prop := ∀ (v : S), v ∈ x → v ∈ y

instance : HasSubset S := ⟨Subset⟩

@[simp] lemma subset_def (x y : S) : x ⊆ y ↔ ∀ v, v ∈ x → v ∈ y := by rfl

/-- y ⊂ x -/
abbrev SSubset (x y : S) : Prop := x ⊆ y ∧ x ≠ y

instance : HasSSubset S := ⟨SSubset⟩

lemma sSubset_def (x y : S) : x ⊂ y ↔ (∀ v, v ∈ x → v ∈ y) ∧ x ≠ y := by rfl

lemma exists_mem_of_sdiff (x y : S) (h : x ⊂ y) : ∃ z, z ∈ y ∧ z ∉ x := by
  simp only [sSubset_def, ne_eq] at h
  by_contra! hn
  have hf (u : S) : u ∈ x ↔ u ∈ y := by apply Iff.intro <;> intro a <;> simp_all only
  simp_all [exten_prop]

lemma exists_powerset_aux (u x y Px : S) (hPx : ∀ (u : S), u ∈ Px ↔ u ⊆ x) :
    u ⊆ (x ◁ y) ↔ (u ∈ Px) ∨ (∃ v ∈ Px, u = v ◁ y) := by
  simp only [subset_def] at *
  refine ⟨?_, by aesop⟩
  intro hu; simp only [mem_enlarge] at hu
  by_cases y_in_u : y ∈ u
  · right; use u ∩ x
    refine ⟨by simp_all, by simp only [enlarge, mem_inter]; aesop⟩
  · left; rw [hPx]
    intros v hv; specialize hu v hv; aesop

theorem exists_powerset (x : S) : ∃ (z : S), ∀ (u : S), u ∈ z ↔ u ⊆ x := by
  induction x using induction with
  | base => use {∅}; simp [exten_prop]
  | step x y hx _ =>
    rcases hx with ⟨Px, hPx⟩
    have : (∀ v ∈ Px, ∃! u, u = v ◁ y) := by intros v _; use v ◁ y; simp_all
    let z := setOfImage (n := 1) Px (fun v u ↦ u = v ◁ y) (&1 =' (.func ◁' ![&0, .var (.inl 0)]))
        (by refine IsAtomic.isQF ?_; exact
          IsAtomic.equal ((var ∘ Sum.inr) 1) (func ◁' ![(var ∘ Sum.inr) 0, var (Sum.inl 0)]))
        (![y]) (by simp) this
    use Px ∪ z
    intro u
    rw [exists_powerset_aux u x y Px hPx, mem_union, mem_setOfImage]
  | n => exact 0
  | f => exact ∃' ∀' ((&2 ∈' &1) ⇔ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &0))))
  | t => rename_i a; exact Fin.elim0 a
  | hP => simp only [subset_def, Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_ex,
    Nat.succ_eq_add_one, realize_all, realize_iff, realize_rel, instStructureHFLangOfHF_RelMap,
    Matrix.cons_val_zero, Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons,
    realize_imp]; rfl

/-- Power set. Defined through u ∈ PowerSet x ↔ SubsetEq u x. -/
def powerset (x : S) : S := (exists_powerset x).choose

lemma mem_powerset (x : S) : ∀ (u : S), u ∈ powerset x ↔ u ⊆ x :=
  (exists_powerset x).choose_spec

lemma found_prop_aux (x z : S) (h : ∀ w ∈ z, w ∩ z ≠ ∅) : x ∉ z ∧ x ∩ z = ∅ := by
  simp only [ne_eq, exten_prop, mem_inter, in_empty_iff_false, iff_false, not_and, not_forall,
    Classical.not_imp, not_not] at *
  revert h
  induction x using induction with
  | base =>
    intro h
    refine ⟨?_, by simp_all⟩
    by_contra hn
    specialize h ∅ hn; simp_all
  | step x y hx hy =>
    intro h; specialize hx h; specialize hy h
    rcases hx with ⟨_, hx2⟩; rcases hy with ⟨hy1, hy2⟩
    refine ⟨?_, by simp only [mem_enlarge]; aesop⟩
    by_contra hn; specialize h (x ◁ y) hn
    simp only [mem_enlarge] at h
    rcases h with ⟨u, ⟨h, _⟩⟩
    refine h.elim (by intro _; simp_all) (by intro _; simp_all)
  | n => exact 1
  | f => exact (∀' ((&1 ∈' .var (.inl 0)) ⟹ (∃' ((&2 ∈' &1) ⊓ (&2 ∈' .var (.inl 0)))))) ⟹
      ((∼(&0 ∈' .var (.inl 0))) ⊓ (∀' ((&1 ∈' &0) ⟹ ∼(&1 ∈' .var (.inl 0)))))
  | t => exact z
  | hP => simp only [exists_prop, Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_imp,
    realize_all, Nat.succ_eq_add_one, realize_rel, instStructureHFLangOfHF_RelMap,
    Matrix.cons_val_zero, Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons,
    Sum.elim_inl, realize_ex, realize_inf, realize_not]; rfl

theorem found_prop (z : S) : z ≠ ∅ → ∃ w, w ∈ z ∧ w ∩ z = ∅ := by
  rw [not_imp_comm, not_exists, exten_prop]
  intro h; simp only [not_and] at h
  intro u; simp_all [found_prop_aux u z h]

instance mem_irrefl : IsIrrefl S (· ∈ ·) where
  irrefl := by
    intro x
    obtain ⟨w, hw⟩ := found_prop ({x} : S) (by simp_rw [ne_eq, exten_prop]; simp_all)
    simp_rw [exten_prop, mem_inter, mem_singleton, in_empty_iff_false] at hw
    aesop

@[simp] lemma in_itself_iff_false (x : S) : x ∈ x ↔ False := by
  refine ⟨irrefl x, by simp only [false_implies]⟩


lemma ne_of_mem (x y : S) (h : x ∈ y) : x ≠ y := by
  by_contra!
  subst x
  rwa [← in_itself_iff_false y]

/-- The set is transitive. -/
abbrev IsTrans (x : S) : Prop := ∀ y ∈ x, y ⊆ x

lemma isTrans_mem (x y z : S) (trans : IsTrans x) (y_in_x : y ∈ x) (z_in_y : z ∈ y) :
    z ∈ x := by apply trans <;> assumption

/-- The set is an ordinal. -/
abbrev IsOrd (k : S) : Prop := IsTrans k ∧ ∀ l ∈ k, IsTrans l

lemma empty_isOrd : IsOrd (∅ : S) := by unfold IsOrd IsTrans; simp_all

/-- The successor of a set. -/
abbrev succ (x : S) : S := x ◁ x

lemma ne_succ (x : S) : x ≠ succ x := by
  intro h
  simp_rw [exten_prop, mem_enlarge] at h
  simp_all

namespace IsOrd

lemma mem_isOrd (k l : S) (ord : IsOrd k) (l_in_k : l ∈ k) : IsOrd l := by
  refine ⟨ord.2 l l_in_k, ?_⟩
  intros m m_in_l
  apply ord.2
  exact isTrans_mem k l m ord.1 l_in_k m_in_l

lemma mem_asymm (k l : S) (ord_k : IsOrd k) (k_in_l : k ∈ l) (l_in_k : l ∈ k) :
    False := by
  apply ord_k.1 l l_in_k at k_in_l
  rwa [← in_itself_iff_false k]

lemma empty_of_mem_and_disjoint (x w : S) (ord : IsOrd x) (w_in_x : w ∈ x)
    (disj : w ∩ x = ∅) : w = ∅ := by
  simp only [exten_prop, mem_inter, in_empty_iff_false, iff_false, not_and] at disj
  apply ord.1 at w_in_x
  rw [HFSet.empty]
  simp_all

lemma empty_is_mem (x : S) (ord : IsOrd x) (ne_emp : x ≠ ∅) : ∅ ∈ x := by
  obtain ⟨w, ⟨w_in_x, disj⟩⟩ := found_prop x ne_emp
  apply empty_of_mem_and_disjoint x w ord w_in_x at disj
  subst w; assumption

lemma succ_isOrd (x : S) (ord : IsOrd x) : IsOrd (succ x) := by
  unfold IsOrd IsTrans succ
  simp only [mem_enlarge, subset_def]
  constructor
  · intros y h v v_in_y
    left
    refine h.elim (by intro h; exact isTrans_mem x y v ord.1 h v_in_y) (by intro h; rwa [← h])
  · intros y h z z_in_y v v_in_z
    rcases h with y_in_x | y_eq_x
    · apply mem_isOrd x y ord at y_in_x
      exact isTrans_mem y z v y_in_x.1 z_in_y v_in_z
    · subst y
      exact isTrans_mem x z v ord.1 z_in_y v_in_z

lemma iff_succ_isOrd (x : S) : IsOrd x ↔ IsOrd (succ x) := by
  refine ⟨succ_isOrd x, ?_⟩
  intro h
  exact mem_isOrd (succ x) x h (by simp)

lemma succ_is_not_mem (k : S) (ord : IsOrd k) : succ k ∉ k := by
  intro succ_k_in_k
  apply ord.1 (succ k) at succ_k_in_k
  specialize succ_k_in_k k (by simp)
  rwa [← in_itself_iff_false k]

lemma comparability_aux1 (h : ∃ (k l : S), IsOrd k ∧ IsOrd l ∧ k ∉ l ∧ k ≠ l ∧ l ∉ k) :
    ∃ (k0 : S), IsOrd k0 ∧ (∀ m ∈ k0, ∀ l, IsOrd l → (m ∈ l ∨ m = l ∨ l ∈ m))
    ∧ (∃ l, IsOrd l ∧ (k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0)) := by
  rcases h with ⟨k, ⟨l, ⟨ord_k, ⟨ord_l, hkl⟩⟩⟩⟩
  let K := setOfMem (n := 0) (powerset k)
    (fun k0 ↦ (((∀ y ∈ k0, ∀ v ∈ y, v ∈ k0) ∧ (∀ y ∈ k0, ∀ y_1 ∈ y, ∀ v ∈ y_1, v ∈ y)) ∧
    ∃ l, ((∀ y ∈ l, ∀ v ∈ y, v ∈ l) ∧ ∀ y ∈ l, ∀ y_1 ∈ y, ∀ v ∈ y_1, v ∈ y) ∧
    k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0)) (((∀' ((&1 ∈' &0) ⟹ (∀' ((&2 ∈' &1) ⟹ (&2 ∈' &0)))))
    ⊓ (∀' ((&1 ∈' &0) ⟹ (∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &1))))))))
    ⊓ (∃' (((∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &1)))))
    ⊓ (∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (∀' ((&4 ∈' &3) ⟹ (&4 ∈' &2))))))))
    ⊓ ((∼(&0 ∈' &1)) ⊓ (∼(&0 =' &1)) ⊓  (∼(&1 ∈' &0))))))
    (![]) (by simp [Fin.snoc, show (4 : Fin 5).1 = 4 by rfl, show (3 : Fin 5).1 = 3 by rfl,
      show (3: Fin 4).1 = 3 by rfl]; intros _ _ _; constructor <;> intro h <;>
      rcases h with ⟨l, ⟨⟨hl1, hl2⟩, hl3⟩⟩ <;> use l <;> simp only [hl3,
        not_false_eq_true, and_self, and_true] <;> refine ⟨hl1, hl2⟩)
  have K_ne_emp : K ≠ ∅ := by
    rw [ne_empty_iff_exists_mem]
    use k
    rw [mem_setOfMem, mem_powerset, subset_def]
    refine ⟨by simp, ⟨by assumption, by use l; refine ⟨ord_l, hkl⟩⟩⟩
  obtain ⟨k0, ⟨k0_in_K, k0_K_disj⟩⟩ := found_prop K K_ne_emp
  rw [mem_setOfMem] at k0_in_K
  rcases k0_in_K with ⟨k0_power_k, ⟨ord_k0, hk0⟩⟩
  refine ⟨k0, by exact ord_k0, ⟨?_, by exact hk0⟩⟩
  by_contra! hn
  rcases hn with ⟨r0, ⟨r0_in_k0, ⟨l0, ⟨ord_l0, hr0l0⟩⟩⟩⟩
  simp only [empty, mem_inter] at k0_K_disj
  refine k0_K_disj r0 ⟨r0_in_k0, ?_⟩
  rw [mem_setOfMem, mem_powerset] at *
  have r0_in_k : r0 ∈ k := by simp_all
  apply ord_k.1 at r0_in_k
  refine ⟨r0_in_k, ⟨mem_isOrd k0 r0 ord_k0 r0_in_k0, ⟨l0, ⟨ord_l0, hr0l0⟩⟩⟩⟩

lemma comparability_aux2 (k0 : S) (h : ∃ (l : S), IsOrd l ∧ k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0) :
    ∃ (l0 : S), IsOrd l0 ∧ (∀ p ∈ l0, k0 ∈ p ∨ k0 = p ∨ p ∈ k0)
    ∧ (k0 ∉ l0 ∧ k0 ≠ l0 ∧ l0 ∉ k0) := by
  rcases h with ⟨l, ⟨ord_l, hk0l⟩⟩
  let L := setOfMem (n := 1) (powerset l)
    (fun l0 ↦ ((∀ y ∈ l0, ∀ v ∈ y, v ∈ l0) ∧ (∀ y ∈ l0, ∀ y_1 ∈ y, ∀ v ∈ y_1, v ∈ y) ∧
    (k0 ∉ l0) ∧ (k0 ≠ l0) ∧ (l0 ∉ k0))) ((∀' ((&1 ∈' &0) ⟹ (∀' ((&2 ∈' &1) ⟹ (&2 ∈' &0)))))
    ⊓ (∀' ((&1 ∈' &0) ⟹ (∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &1)))))))
    ⊓ (∼((.var (.inl 0)) ∈' &0)) ⊓ (∼((.var (.inl 0)) =' &0)) ⊓ (∼(&0 ∈' (.var (.inl 0)))))
    (![k0]) (by simp [Fin.snoc, show (3 : Fin 4).1 = 3 by rfl]; tauto)
  have L_ne_emp : L ≠ ∅ := by
    rw [ne_empty_iff_exists_mem]
    use l
    rw [mem_setOfMem, mem_powerset, subset_def]
    refine ⟨by simp, ⟨ord_l.1, ⟨ord_l.2, hk0l⟩⟩⟩
  obtain ⟨l0, ⟨l0_in_L, l0_L_disj⟩⟩ := found_prop L L_ne_emp
  rw [mem_setOfMem] at l0_in_L
  rcases l0_in_L with ⟨l0_power_l, ⟨ord_l0_1, ⟨ord_l0_2, hk0l0⟩⟩⟩
  refine ⟨l0, ⟨ord_l0_1, ord_l0_2⟩, ⟨?_, by exact hk0l0⟩⟩
  by_contra! hn
  rcases hn with ⟨q0, ⟨q0_in_l0, hk0q0⟩⟩
  simp only [empty, mem_inter] at l0_L_disj
  refine l0_L_disj q0 ⟨q0_in_l0, ?_⟩
  rw [mem_setOfMem, mem_powerset] at *
  have q0_in_l : q0 ∈ l := by simp_all
  apply ord_l.1 at q0_in_l
  apply mem_isOrd l0 q0 (by refine ⟨ord_l0_1, ord_l0_2⟩) at q0_in_l0
  refine ⟨q0_in_l, ⟨q0_in_l0.1, ⟨q0_in_l0.2, hk0q0⟩⟩⟩

lemma comparability_aux3 (k0 l0 : S) (ord_l0 : IsOrd l0)
    (forall_in_l0 : ∀ p ∈ l0, k0 ∈ p ∨ k0 = p ∨ p ∈ k0) (hl0 : k0 ∉ l0 ∧ k0 ≠ l0 ∧ l0 ∉ k0) :
    l0 ⊂ k0 := by
  refine ⟨?_, by intro a; subst a; simp_all⟩
  intros p p_in_l0
  specialize forall_in_l0 p p_in_l0
  rcases forall_in_l0 with k0_in_p | k0_eq_p | p_in_k0
  · apply ord_l0.1 at p_in_l0
    specialize p_in_l0 k0 k0_in_p
    exfalso; apply hl0.1
    assumption
  · subst p
    exfalso; apply hl0.1
    assumption
  · assumption

theorem comparability (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) :
    k ∈ l ∨ k = l ∨ l ∈ k := by
  revert k l
  by_contra! hn
  obtain ⟨k0, ⟨ord_k0, ⟨forall_in_k0, hk0⟩⟩⟩ := comparability_aux1 hn
  obtain ⟨l0, ⟨ord_l0, ⟨forall_in_l0, hl0⟩⟩⟩ := comparability_aux2 k0 hk0
  obtain ⟨m, ⟨m_in_k0 , m_notin_l0⟩⟩ :=
    exists_mem_of_sdiff l0 k0 (comparability_aux3 k0 l0 ord_l0 forall_in_l0 hl0)
  specialize forall_in_k0 m m_in_k0 l0 ord_l0
  simp only [m_notin_l0, false_or] at forall_in_k0
  refine forall_in_k0.elim (by intro h; simp_all) ?_
  intro l0_in_m
  apply ord_k0.1 m m_in_k0 at l0_in_m
  simp_all

theorem exclusive_comparability (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) :
  (k ∈ l ∧ (k ≠ l ∧ l ∉ k)) ∨ (k = l ∧ (k ∉ l ∧ l ∉ k)) ∨ (l ∈ k ∧ (k ∉ l ∧ k ≠ l)) := by
  by_cases k_in_l : k ∈ l
  · left
    refine ⟨k_in_l, ⟨ne_of_mem k l k_in_l, ?_⟩⟩
    by_contra l_in_k
    apply mem_asymm k l ord_k k_in_l l_in_k
  · by_cases k_eq_l : k = l
    · right; left
      refine ⟨k_eq_l, ⟨k_in_l, by subst k; exact k_in_l⟩⟩
    · right; right
      apply comparability k l ord_k at ord_l
      simp only [k_in_l, not_false_eq_true, k_eq_l, false_or, ne_eq, and_self, and_true] at *
      exact ord_l

@[simp] lemma sSubset_iff_mem (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) :
    k ⊂ l ↔ k ∈ l := by
  constructor
  · intro k_subset_l
    apply comparability k l ord_k at ord_l
    simp only [k_subset_l.2, false_or] at ord_l
    refine ord_l.elim (fun a ↦ a) ?_
    intro l_in_k
    apply k_subset_l.1 at l_in_k
    exfalso; rwa [← in_itself_iff_false l]
  · intro k_in_l
    refine ⟨by apply ord_l.1; exact k_in_l, ne_of_mem k l k_in_l⟩

lemma succ_eq_or_succ_mem (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) (l_in_k : l ∈ k) :
  succ l = k ∨ succ l ∈ k := by
  have h := comparability k (succ l) ord_k (succ_isOrd l ord_l)
  refine h.elim ?_ (by rw [eq_comm]; exact fun a ↦ a)
  intro k_in_succ_l; simp only [mem_enlarge] at k_in_succ_l
  rcases k_in_succ_l with k_in_l | k_eq_l
  · exfalso; apply mem_asymm k l ord_k k_in_l l_in_k
  · exfalso; apply ne_of_mem l k l_in_k; rw [k_eq_l]

lemma mem_iff_succ_mem (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) :
    l ∈ k ↔ succ l ∈ succ k := by
  simp only [mem_enlarge]
  refine ⟨by intro l_in_k; rw [Or.comm]; exact succ_eq_or_succ_mem k l ord_k ord_l l_in_k , ?_⟩
  intro h
  refine h.elim (by intro h; exact isTrans_mem k (succ l) l ord_k.1 h (by simp)) ?_
  intro h2
  subst k
  simp_all

lemma succ_inj (k l : S) (ord_k : IsOrd k) (succ_eq : succ k = succ l) :
    k = l := by
  by_contra! k_ne_l
  simp_rw [exten_prop, mem_enlarge] at succ_eq; have succ_eq' := succ_eq
  specialize succ_eq l; specialize succ_eq' k
  simp only [in_itself_iff_false, k_ne_l, eq_comm, k_ne_l, or_false, or_true, iff_true,
    true_iff] at *
  apply mem_asymm k l ord_k succ_eq' succ_eq

lemma eq_iff_succ_eq (k l : S) (ord_k : IsOrd k) :
    k = l ↔ succ k = succ l := by refine ⟨by intro h; rw [h], succ_inj k l ord_k⟩

lemma exists_max_of_set_aux (x y : S) (set_of_ord : ∀ k ∈ x ◁ y, IsOrd k)
    (x_has_max : ∃ l ∈ x, ∀ k ∈ x, (k ∈ l ∨ k = l)) :
    ∃ l ∈ x ◁ y, ∀ k ∈ x ◁ y, (k ∈ l ∨ k = l) := by
  rcases x_has_max with ⟨max_x, ⟨max_x_in_x, h_max_x⟩⟩
  have ord_max_x : IsOrd max_x := set_of_ord max_x (by simp_all)
  have ord_y :  IsOrd y := set_of_ord y (by simp)
  by_cases max_x_in_y : max_x ∈ y
  · use y
    simp only [mem_enlarge, or_true, true_and]
    intros k hk
    refine hk.elim ?_ (fun a ↦ Or.inr a)
    intro k_in_x; specialize h_max_x k k_in_x
    left
    refine h_max_x.elim (isTrans_mem y max_x k ord_y.1 max_x_in_y)
      (by intro k_eq_max; subst k; exact max_x_in_y)
  · use max_x
    simp only [mem_enlarge, max_x_in_x, true_or, true_and]
    intros k hk
    refine hk.elim (h_max_x k) ?_
    intro k_eq_y; subst k
    have compar := comparability y max_x ord_y ord_max_x
    simp_all

theorem exists_max_of_set (x : S) (set_of_ord : ∀ k ∈ x, IsOrd k) (ne_emp : x ≠ ∅) :
    ∃ l ∈ x, ∀ k ∈ x, (k ∈ l ∨ k = l) := by
  induction x using induction with
  | base =>  exfalso; apply ne_emp; rfl
  | step x y hx _ =>
    specialize hx
      (by simp_rw [mem_enlarge] at *; intros k k_in_x; apply set_of_ord k; left; exact k_in_x)
    by_cases x_eq_emp : x = ∅
    · use y
      simp [x_eq_emp]
    · exact exists_max_of_set_aux x y set_of_ord (hx x_eq_emp)
  | n => exact 0
  | f => exact ((∀' ((&1 ∈' &0) ⟹ ((∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &1)))))
    ⊓ (∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (∀' ((&4 ∈' &3) ⟹ (&4 ∈' &2))))))))))
    ⟹ (∼(&0 =' (.func ∅' Fin.elim0))) ⟹ (∃' ((&1 ∈' &0) ⊓ ∀' ((&2 ∈' &0) ⟹
    ((&2 ∈' &1) ⊔ (&2 =' &1))))))
  | t => rename_i a; exact Fin.elim0 a
  | hP => simp only [ne_eq, Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_imp,
    realize_all, Nat.succ_eq_add_one, realize_rel, instStructureHFLangOfHF_RelMap,
    Matrix.cons_val_zero, Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons,
    realize_inf, realize_not, realize_bdEqual, Term.realize_func, instStructureHFLangOfHF_funMap,
    realize_ex, realize_sup]; rfl

lemma exists_min_of_set_aux (x y : S) (set_of_ord : ∀ k ∈ x ◁ y, IsOrd k)
    (x_has_min : ∃ l ∈ x, ∀ k ∈ x, (l ∈ k ∨ l = k)) :
    ∃ l ∈ x ◁ y, ∀ k ∈ x ◁ y, (l ∈ k ∨ l = k) := by
  rcases x_has_min with ⟨min_x, ⟨min_x_in_x, h_min_x⟩⟩
  have ord_min_x : IsOrd min_x := set_of_ord min_x (by simp_all)
  have ord_y :  IsOrd y := set_of_ord y (by simp)
  by_cases y_in_min_x : y ∈ min_x
  · use y
    simp only [mem_enlarge, or_true, true_and] at *
    intros k hk
    refine hk.elim ?_ (fun a ↦ Or.inr (id (Eq.symm a)))
    intro k_in_x; specialize h_min_x k k_in_x
    left
    refine h_min_x.elim ?_ (by intro k_eq_min; subst k; exact y_in_min_x)
    intro min_x_in_k; apply isTrans_mem k min_x y (set_of_ord k hk).1 min_x_in_k y_in_min_x
  · use min_x
    simp only [mem_enlarge, min_x_in_x, true_or, true_and]
    intros k hk
    refine hk.elim (h_min_x k) ?_
    intro k_eq_y; subst k
    have compar := comparability min_x y ord_min_x ord_y
    simp_all

theorem exists_min_of_set (x : S) (set_of_ord : ∀ k ∈ x, IsOrd k) (ne_emp : x ≠ ∅) :
    ∃ l ∈ x, ∀ k ∈ x, (l ∈ k ∨ l = k) := by
  induction x using induction with
  | base => exfalso; apply ne_emp; rfl
  | step x y hx _ =>
    specialize hx
      (by simp_rw [mem_enlarge] at *; intros k k_in_x; apply set_of_ord k; left; exact k_in_x)
    by_cases x_eq_emp : x = ∅
    · use y
      simp [x_eq_emp]
    · exact exists_min_of_set_aux x y set_of_ord (hx x_eq_emp)
  | n => exact 0
  | f => exact ((∀' ((&1 ∈' &0) ⟹ ((∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &1)))))
    ⊓ (∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (∀' ((&4 ∈' &3) ⟹ (&4 ∈' &2))))))))))
    ⟹ (∼(&0 =' (.func ∅' Fin.elim0))) ⟹ (∃' ((&1 ∈' &0) ⊓ ∀' ((&2 ∈' &0) ⟹
    ((&1 ∈' &2) ⊔ (&1 =' &2))))))
  | t => rename_i a; exact Fin.elim0 a
  | hP => simp only [ne_eq, Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_imp,
    realize_all, Nat.succ_eq_add_one, realize_rel, instStructureHFLangOfHF_RelMap,
    Matrix.cons_val_zero, Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons,
    realize_inf, realize_not, realize_bdEqual, Term.realize_func, instStructureHFLangOfHF_funMap,
    realize_ex, realize_sup]; rfl

theorem exists_pred (k : S) (ord_k : IsOrd k) (ne_emp : k ≠ ∅) :
    ∃! l, succ l = k := by
  obtain ⟨max_k, ⟨max_k_in_k, h_max_k⟩⟩ := exists_max_of_set k
    (by intros l hl; exact mem_isOrd k l ord_k hl) ne_emp
  have ord_max_k : IsOrd max_k := mem_isOrd k max_k ord_k max_k_in_k
  rcases succ_eq_or_succ_mem k max_k ord_k ord_max_k max_k_in_k with
    succ_max_k_eq_k | succ_max_k_in_k
  · use max_k
    simp only [← succ_max_k_eq_k, true_and, eq_comm]
    intro y
    exact succ_inj max_k y ord_max_k
  · specialize h_max_k (succ max_k) succ_max_k_in_k
    simp [succ_is_not_mem max_k ord_max_k, eq_comm, ne_succ max_k] at h_max_k

/-- The predecessor of a non-empty ordinal. -/
def pred (k : S) (ord : IsOrd k) (ne_emp : k ≠ ∅) : S := (exists_pred k ord ne_emp).choose

lemma succ_pred (k : S) (ord : IsOrd k) (ne_emp : k ≠ ∅) :
    succ (pred k ord ne_emp) = k := by
  have := (exists_pred k ord ne_emp).choose_spec; simp only at this
  rcases this with ⟨this, _⟩
  rwa [pred]

lemma pred_isOrd (k : S) (ord : IsOrd k) (ne_emp : k ≠ ∅) : IsOrd (pred k ord ne_emp) := by
  rwa [iff_succ_isOrd, succ_pred]

end IsOrd

variable (S) in
/-- The ordinal subtype.-/
def Ord : Type u := {k : S // IsOrd k}

namespace Ord

@[simp] lemma eq_iff (k l : Ord S) : k = l ↔ k.1 = l.1 := Subtype.ext_iff

instance : EmptyCollection (Ord S) := ⟨⟨(∅ : S), empty_isOrd⟩⟩

instance le : LE (Ord S) := ⟨fun k l => k.1 ∈ l.1 ∨ k = l⟩

instance lt : LT (Ord S) := ⟨fun k l => k ≤ l ∧ ¬l ≤ k⟩

lemma le_aux (k l : Ord S) : k ≤ l ↔ k.1 ∈ l.1 ∨ k = l := Iff.rfl

lemma lt_aux (k l : Ord S) : k < l ↔ k ≤ l ∧ ¬l ≤ k := Iff.rfl

lemma lt_iff (k l : Ord S) : k < l ↔ k.1 ∈ l.1 := by
  simp only [lt_aux, le_aux, eq_iff, not_or, Eq.comm]
  constructor
  · intro h; rcases h with ⟨h1, _⟩
    refine h1.elim ?_ (by simp_all only [or_false, false_implies])
    exact fun a ↦ a
  · intro h
    refine ⟨by left; exact h, ?_⟩
    have := IsOrd.exclusive_comparability k.1 l.1 k.2 l.2
    simp_all

lemma le_iff (k l : Ord S) : k ≤ l ↔ k < l ∨ k = l := by simp [le_aux, lt_iff]

@[simp] lemma lt_empty_iff_false (k : Ord S) : k < (∅ : Ord S) ↔ False := by
  simp only [lt_iff, iff_false]
  exact notin_empty k.1

@[simp] lemma lt_itself_iff_false (k : Ord S) : k < k ↔ False := by simp [lt_iff]

lemma ne_of_lt (k l : Ord S) (h : k < l) : k ≠ l := by
  simp only [lt_iff, ne_eq, eq_iff] at *
  exact ne_of_mem k.1 l.1 h

lemma lt_trans (k l m : Ord S) (k_lt_l : k < l) (l_lt_m : l < m) : k < m := by
  simp only [lt_iff] at *
  exact isTrans_mem m.1 l.1 k.1 m.2.1 l_lt_m k_lt_l

/-- The successor of an ordinal. -/
def succ (k : Ord S) : Ord S := ⟨_, IsOrd.succ_isOrd _ k.2⟩

lemma ne_succ (k : Ord S) : k ≠ succ k := by
  simp only [ne_eq, eq_iff]
  exact HFSet.ne_succ k.1

lemma lt_asymm (k l : Ord S) (k_lt_l : k < l) (l_lt_k : l < k) :
    False := by
  simp only [lt_iff] at *
  exact IsOrd.mem_asymm k.1 l.1 k.2 k_lt_l l_lt_k

lemma empty_is_lt (k : Ord S) (ne_emp : k ≠ ∅) : ∅ < k := by
  simp only [ne_eq, eq_iff, lt_iff] at *
  exact IsOrd.empty_is_mem k.1 k.2 ne_emp

lemma succ_is_not_lt (k : Ord S) : ¬(succ k < k) := by
  simp only [lt_iff]
  exact IsOrd.succ_is_not_mem k.1 k.2

theorem comparability (k l : Ord S) : k < l ∨ k = l ∨ l < k := by
  simp only [lt_iff, eq_iff]
  exact IsOrd.comparability k.1 l.1 k.2 l.2

theorem exclusive_comparability (k l : Ord S) :
    (k < l ∧ ¬(k = l ∨ l < k)) ∨ (k = l ∧ ¬(k < l ∨ l < k)) ∨ (l < k ∧ ¬(k < l ∨ k = l)) := by
  simp only [lt_iff, eq_iff, not_or]
  push_neg
  exact IsOrd.exclusive_comparability k.1 l.1 k.2 l.2

/-- k ⊆ l -/
abbrev Subset (k l : Ord S) : Prop := ∀ (m : Ord S), m < k → m < l

instance : HasSubset (Ord S) := ⟨Subset⟩

lemma subset_def (k l : Ord S) : k ⊆ l ↔ ∀ m, m < k → m < l := by rfl

lemma subset_iff (k l : Ord S) : k ⊆ l ↔ k.1 ⊆ l.1 := by
  simp only [subset_def, lt_iff, HFSet.subset_def]
  constructor
  · intros h m m_in_k
    specialize h ⟨m, IsOrd.mem_isOrd k.1 m k.2 m_in_k⟩
    exact h m_in_k
  · intros h m m_in_k
    exact h m.1 m_in_k

/-- k ⊂ l -/
abbrev SSubset (k l : Ord S) : Prop := k ⊆ l ∧ k ≠ l

instance : HasSSubset (Ord S) := ⟨SSubset⟩

lemma sSubset_def (k l : Ord S) : k ⊂ l ↔ (∀ m, m < k → m < l) ∧ k ≠ l := by rfl

lemma sSubset_iff (k l : Ord S) : k ⊂ l ↔ k.1 ⊂ l.1 := by
  simp only [sSubset_def, lt_iff, ne_eq, eq_iff, HFSet.sSubset_def, and_congr_left_iff]
  intro _
  have := subset_iff k l
  simp [subset_def, lt_iff] at this
  exact this

@[simp] lemma sSubset_iff_lt (k l : Ord S) : k ⊂ l ↔ k < l := by
  simp only [sSubset_iff, lt_iff]
  exact IsOrd.sSubset_iff_mem k.1 l.1 k.2 l.2

lemma succ_eq_or_succ_lt (k l : Ord S) (l_lt_k : l < k) : succ l = k ∨ succ l < k := by
  simp only [lt_iff, eq_iff] at *
  exact IsOrd.succ_eq_or_succ_mem k.1 l.1 k.2 l.2 l_lt_k

lemma succ_inj (k l : Ord S) (succ_eq : succ k = succ l) : k = l := by
  simp only [eq_iff] at *
  exact IsOrd.succ_inj k.1 l.1 k.2 succ_eq

lemma le_trans (k l m : Ord S) : k ≤ l → l ≤ m → k ≤ m := by
  intros k_le_l l_le_m
  simp [le_aux] at *
  cases k_le_l with
  | inl h_k_le_l =>
    cases l_le_m with
    | inl h_l_le_m => exact Or.inl (m.2.1 _ h_l_le_m _ h_k_le_l)
    | inr h_l_eq_m => exact Or.inl (h_l_eq_m ▸ h_k_le_l)
  | inr h_k_eq_l =>
    cases l_le_m with
    | inl h_l_le_m => exact Or.inl (h_k_eq_l.symm ▸ h_l_le_m)
    | inr h_l_eq_m => exact Or.inr (h_k_eq_l.symm ▸ h_l_eq_m)

lemma le_antisymm (k l : Ord S) : k ≤ l → l ≤ k → k = l := by
  simp only [le_aux, eq_iff]
  intros h1 h2
  refine h1.elim ?_ (fun a ↦ a)
  refine h2.elim ?_ (fun a _↦ id (Eq.symm a))
  intros h3 h4; exfalso
  exact IsOrd.mem_asymm k.1 l.1 k.2 h4 h3

lemma le_total (k l : Ord S) : k ≤ l ∨ l ≤ k := by
  simp only [le_aux, eq_iff, Eq.comm]
  cases IsOrd.comparability k.1 l.1 k.2 l.2 with
  | inl h => simp_all only [true_or]
  | inr h_1 =>
    cases h_1 with
    | inl h => simp_all only [in_itself_iff_false, or_true, or_self]
    | inr h_2 => simp_all only [true_or, or_true]

instance le_totalOrder : LinearOrder (Ord S) where
  le := fun k l => k ≤ l
  le_refl := by simp [le_iff]
  le_trans := le_trans
  le_antisymm := le_antisymm
  le_total := le_total
  decidableLE := inferInstance

instance lt_sTotalOrder : IsStrictTotalOrder (Ord S) (· < ·) where
  trichotomous := comparability
  irrefl := fun a ↦ gt_irrefl a
  trans := lt_trans

/-- The predecessor of a non-empty ordinal -/
def pred (k : Ord S) (ne_emp : k ≠ ∅) : Ord S := ⟨_, IsOrd.pred_isOrd _ k.2
  (by simp only [ne_eq, eq_iff] at ne_emp; exact ne_emp)⟩

lemma succ_pred (k : Ord S) (ne_emp : k ≠ ∅) : succ (pred k ne_emp) = k := by
  simp only [eq_iff]
  exact IsOrd.succ_pred k.1 k.2 (by simp only [ne_eq, eq_iff] at ne_emp; exact ne_emp)

lemma pred_element_eq (k : Ord S) (ne_emp : k ≠ ∅) :
    (pred k ne_emp).1 = IsOrd.pred k.1 k.2 (by simp only [ne_eq, eq_iff] at ne_emp; exact ne_emp)
    := by rfl

lemma pred_lt (k : Ord S) (ne_emp : k ≠ ∅) : pred k ne_emp < k := by
  simp only [lt_iff]
  rw [IsOrd.mem_iff_succ_mem, pred_element_eq, IsOrd.succ_pred]
  · simp
  · exact k.2
  · rw [pred_element_eq]
    exact IsOrd.pred_isOrd k.1 k.2 (by simp only [ne_eq, eq_iff] at ne_emp; exact ne_emp)

lemma forall_lt_le_pred (k : Ord S) (ne_emp : k ≠ ∅) : ∀ l < k, l ≤ pred k ne_emp := by
  intros l l_lt_k
  simp only [lt_iff, le_iff, eq_iff] at *
  rw [IsOrd.mem_iff_succ_mem, IsOrd.eq_iff_succ_eq, pred_element_eq,
    IsOrd.succ_pred k.1 k.2 (by simp only [ne_eq, eq_iff] at ne_emp; exact ne_emp), Or.comm]
  · exact IsOrd.succ_eq_or_succ_mem k.1 l.1 k.2 l.2 l_lt_k
  · exact l.2
  · rw [pred_element_eq]
    exact IsOrd.pred_isOrd k.1 k.2 (by simp only [ne_eq, eq_iff] at ne_emp; exact ne_emp)
  · exact l.2

end Ord
end HFSet
