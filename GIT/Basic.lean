import GIT.FirstOrder_reverse
import GIT.Formal

open FirstOrder Language BoundedFormula HF

/-!
# Appendix 1: Axioms and basic results of hereditarily finite set theory

In this file, the first appendix of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness
Theorems' is formalised. It systematically presents the axioms and basic results of the
theory of hereditarily finite sets.

## Main results

- `HFSet.exten_prop`: Extensionality property.
- `HFSet.exists_union`: Existence of the union of two sets.
- `HFSet.exists_sUnion`: Existence of the union of a set of sets.
- `HFSet.comp_scheme`: Comprehension scheme.
- `HFSet.repl_scheme`: Replacement scheme.
- `HFSet.exists_powerset`: Existence of the power set.
- `HFSet.found_prop`: Foundation property.

## Notation

- `◁` : enlarging, see `HFSet.enlarge`.

## References

S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.
-/

/-- Write `∅` instead of `EmptySet`. -/
instance (S : Type) [Lang.Structure S] : EmptyCollection S :=
  ⟨(by
  rename_i inst
  exact inst.1 (∅') Fin.elim0)⟩

/-- Write `∈` instead of `Mem`. -/
instance (S : Type) [Lang.Structure S] : Membership S S := ⟨(by
    rename_i inst;
    intro x y
    exact inst.2 HF.Lang.membershipSymbol ![x, y])⟩

abbrev enlarging {S : Type} [Lang.Structure S] (x y : S) : S := (by
  rename_i inst
  exact inst.1 (◁') ![x, y])

/-- Write `◁` instead of `enlarging`. -/
infixl:90 " ◁ " => enlarging

@[simp]
lemma empty_fun (S : Type) (inst : Lang.Structure S) :
    ∀ (f : Fin 0 → S), inst.funMap (∅') f = ∅ := by
  intro f
  have : f = Fin.elim0 := by ext i; fin_cases i
  rw [this]
  rfl

@[simp]
lemma enlarge_fun (S : Type) (inst : Lang.Structure S) :
    ∀ (f : Fin 2 → S), inst.funMap (◁') f = (f 0 ◁ f 1) := by
  intro f
  have : f = ![f 0, f 1] := by ext i; fin_cases i <;> simp
  rw [this]
  rfl

@[simp]
lemma mem_rel (S : Type) (inst : Lang.Structure S) :
    ∀ (f : Fin 2 → S), inst.RelMap HF.Lang.membershipSymbol f = (f 0 ∈ f 1) := by
  intro f
  have : f = ![f 0, f 1] := by ext i; fin_cases i <;> simp
  rw [this]
  rfl

/-- HFSet class with the axioms of HF. -/
class HFSet (S : Type) [Lang.Structure S] where
  /-- Axiom 1 "for the empty set". -/
  empty (z : S) : z = ∅ ↔ ∀ x, x ∉ z
  /-- Axiom 2 "for enlargement". -/
  enlarge (x y z : S) : z = x ◁ y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y
  /-- Axiom 3: the induction principle. The additional four goals (next to base and step)
  ensure induction is over all formulae in the first-order language of HF rather than over all
  predicates.  -/
  induction (α : S → Prop) (base : α ∅) (step : ∀ x y, α x → α y → α (x ◁ y))
      (n : Nat) (f : Language.BoundedFormula HF.Lang (Fin n) 1) (t : (Fin n) → S)
      (hP : ∀ z, α z ↔ f.Realize t (fun _ ↦ z)) (z : S) : α z

namespace HFSet

namespace Model

lemma empty_aux (s : Type) [Lang.Structure s] : (∀ (z : s), (z = ∅ ↔ ∀ x, x ∉ z)) ↔
    Sentence.Realize s Axiom1  := by
  unfold Axiom1
  simp only [Sentence.Realize, Formula.Realize, Nat.reduceAdd, Fin.isValue, Function.comp_apply,
    realize_all, Nat.succ_eq_add_one, realize_iff, realize_bdEqual, Term.realize_var, Sum.elim_inr,
    Term.realize_func, empty_fun, realize_not, realize_rel, mem_rel, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  rfl

lemma enlarge_aux (s : Type) [Lang.Structure s] :
    (∀ (x y z : s), (z = x ◁ y ↔ ∀ u, u ∈ z ↔ u ∈ x ∨ u = y)) ↔
    Sentence.Realize s Axiom2  := by
  unfold Axiom2
  simp only [enlarge_fun, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Sentence.Realize, Formula.Realize, Nat.reduceAdd, Function.comp_apply, realize_all,
    Nat.succ_eq_add_one, realize_iff, realize_bdEqual, Term.realize_var, Sum.elim_inr, Fin.snoc,
    Fin.val_zero, Nat.ofNat_pos, ↓reduceDIte, Fin.castSucc_castLT, Fin.coe_castLT, zero_lt_one,
    Nat.zero_eq, Fin.coe_fin_one, lt_self_iff_false, cast_eq, Term.realize_func, Fin.val_one,
    Nat.one_lt_ofNat, Fin.val_two, realize_rel, mem_rel, show (3 : Fin 4).1 = 3 by rfl, realize_sup,
    Nat.lt_succ_self]
  refine ⟨by simp_all, by simp_all⟩

lemma induction_aux (S : Type) [Lang.Structure S] (v : α → S) (φ : Lang.BoundedFormula α 1 )
    (f : S → Prop) (hP : ∀ z, (f z ↔ φ.Realize v (fun _ ↦ z))) :
    ((f ∅) → (∀ x y, f x → f y → f (x ◁ y)) → (∀ x, f x))
    ↔
    Formula.Realize (Axiom3 φ) v := by
unfold Axiom3
simp only [hP, enlarge_fun, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
  Matrix.head_cons, Formula.Realize, Nat.reduceAdd, Function.comp_apply, realize_imp, realize_inf,
  realize_all, Nat.succ_eq_add_one, realize_bdEqual, Term.realize_var, Sum.elim_inr, Fin.snoc,
  Fin.coe_fin_one, lt_self_iff_false, ↓reduceDIte, cast_eq, Term.realize_func, empty_fun, forall_eq,
  le_refl, realize_liftAt, zero_lt_one, ↓reduceIte, zero_add, Nat.one_le_ofNat, Fin.addNat_one,
  Fin.val_two, Fin.val_zero, Nat.ofNat_pos, Fin.castSucc_castLT, Fin.coe_castLT, Nat.zero_eq,
  Fin.val_one, Nat.one_lt_ofNat, and_imp]
constructor <;> intros h1 h2 h3 z <;> specialize h1 h2 <;> apply h1 <;> intros x y hx hy
  <;> specialize h3 x y <;> exact h3 (by simp only [Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, enlarge_fun, Fin.castAdd, Fin.castLE, Nat.reduceAdd,
    Fin.coe_fin_one, Fin.zero_eta] at *; exact hx) (hy)

lemma empty (S) [Model S] : ∀ (z : S), z = ∅ ↔ ∀ (x : S), x ∉ z := by
  rename_i inst; rcases inst with ⟨struc, model⟩
  specialize model Axiom1
  simp only [HF.Theory, Set.iUnion_singleton_eq_range, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, true_or, Set.mem_range, Fin.forall_fin_zero_pi, true_implies] at model
  rwa [empty_aux S, models_iff_realize_of_sentence]

lemma enlarge (S) [Model S] : ∀ (x y z : S), z = x ◁ y ↔ ∀ (u : S), u ∈ z ↔ u ∈ x ∨ u = y := by
  rename_i inst; rcases inst with ⟨struc, model⟩
  specialize model Axiom2
  simp only [HF.Theory, Set.iUnion_singleton_eq_range, Set.mem_union, Set.mem_insert_iff,
    Set.mem_singleton_iff, or_true, Set.mem_range,
    true_or, Fin.forall_fin_zero_pi, true_implies] at model
  rwa [enlarge_aux S, models_iff_realize_of_sentence]

lemma induction (S) [Model S] : ∀ (α : S → Prop), α ∅ → (∀ (x y : S), α x → α y → α (x ◁ y)) →
    ∀ (n : ℕ) (f : Lang.BoundedFormula (Fin n) 1) (t : Fin n → S),
    (∀ (z : S), α z ↔ f.Realize t fun _ ↦ z) → ∀ (z : S), α z := by
  intros f h1 h2 n φ v hP
  revert h2 h1
  rw [induction_aux S v φ f hP]
  rename_i inst; rcases inst with ⟨struc, _, model⟩
  specialize model (Axiom3 φ)
  simp only [Scheme, Set.iUnion_singleton_eq_range, Set.mem_range, exists_apply_eq_apply,
    true_implies] at model
  apply model v

instance (S) [Model S] : HFSet S where
  empty := empty S
  enlarge := enlarge S
  induction := induction S

end Model

suppress_compilation

variable {S : Type} [Lang.Structure S] [HFSet S]

lemma notin_empty (x : S) : x ∉ (∅ : S) := by revert x; rw [← empty  ∅]

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
      mem_rel, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
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

lemma pair_eq (x y : S) : pair x y = (∅ ◁ (∅ ◁ x)) ◁ ((∅ ◁ x) ◁ y) := by simp [exten_prop]

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
  | hP =>
    simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_ex, Nat.succ_eq_add_one,
      realize_all, realize_iff, realize_rel, mem_rel, Matrix.cons_val_zero, Term.realize_var,
      Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons, realize_sup, Sum.elim_inl]
    rfl

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
  | hP =>
    simp only [Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_ex, Nat.succ_eq_add_one,
      realize_all, realize_iff, realize_rel, mem_rel, Matrix.cons_val_zero, Term.realize_var,
      Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons, realize_inf]
    rfl

/-- ⋃ x. Defined through z ∈ ⋃ x ↔ (∃ y ∈ x, z ∈ y). -/
def sUnion (x : S) : S := (exists_sUnion x).choose

/-- ⋃ x. Defined through z ∈ ⋃ x ↔ (∃ y ∈ x, z ∈ y). -/
prefix:110 "⋃₀" => sUnion

@[simp] lemma mem_sUnion (x u : S) : (u ∈ ⋃₀ x ↔ (∃ y ∈ x, u ∈ y)) := by
  revert u
  exact (exists_sUnion x).choose_spec

theorem comp_scheme (x : S) (φ : S → Prop) {n} (f : BoundedFormula HF.Lang (Fin n) 1)
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
      realize_all, realize_iff, realize_rel, mem_rel, Matrix.cons_val_zero, Term.realize_var,
      Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons, realize_inf]
    convert Iff.rfl
    rw [realize_liftAt (by norm_num), hφ]
    convert Iff.rfl
    simp_all only [Nat.reduceAdd, Fin.coe_fin_one, lt_self_iff_false, ↓reduceIte]
    ext1 x_2
    simp_all only [Matrix.cons_val_fin_one, Function.comp_apply]
    rfl

/-- Any definable (defined through a formula φ) sublass of a set x is a set — {u ∈ x : φ(u)}. -/
def setOfMem (x : S) (φ : S → Prop) (n : ℕ) (f : BoundedFormula HF.Lang (Fin n) 1) (c : Fin n → S)
    (hφ : ∀ x, φ x ↔ f.Realize c ![x]) : S := (comp_scheme x φ f c hφ).choose

@[simp] lemma mem_setOfMem (x u : S) (φ : S → Prop) (n : ℕ) (f : BoundedFormula HF.Lang (Fin n) 1)
    (c : Fin n → S) (hφ : ∀ x, φ x ↔ f.Realize c ![x]) :
    (u ∈ setOfMem x φ n f c hφ ↔ u ∈ x ∧ φ u) := by
  revert u
  exact (comp_scheme x φ f c hφ).choose_spec

/-- x ∩ y = {u ∈ x : u ∈ y} -/
def inter (x : S) (y : S) : S :=
    setOfMem x (fun z ↦ z ∈ y) 1
      ((&0 ∈' .var (.inl 0))) (![y]) (by simp)

/-- x ∩ y = {u ∈ x : u ∈ y} -/
instance : Inter S := ⟨inter⟩

@[simp] lemma mem_inter (x y u : S) : (u ∈ x ∩ y ↔ u ∈ x ∧ u ∈ y) :=
  mem_setOfMem x u (fun z ↦ z ∈ y) 1 ((&0 ∈' .var (.inl 0))) (![y]) (by simp)

/-- ⋂ x = {u ∈ ⋃ x : ∀ v ∈ x, u ∈ v} -/
def sInter (x : S) : S :=
  setOfMem (⋃₀ x) (fun u ↦ ∀ v ∈ x, u ∈ v) 1
      (∀' ((&1 ∈' .var (.inl 0)) ⟹ (&0 ∈' &1))) ![x] (by simp [Fin.snoc])

/-- ⋂ x = {u ∈ ⋃ x : ∀ v ∈ x, u ∈ v} -/
prefix:110 "⋂₀ " => sInter

@[simp] lemma mem_sInter (x u : S) :
    (u ∈ ⋂₀ x ↔ u ∈ ⋃₀ x ∧ ∀ v ∈ x, u ∈ v) :=
  mem_setOfMem (⋃₀ x) u (fun u ↦ ∀ v ∈ x, u ∈ v) 1
      (∀' ((&1 ∈' .var (.inl 0)) ⟹ (&0 ∈' &1))) ![x] (by simp [Fin.snoc])

lemma inter_enlarge (x y : S) : (x ◁ y) ∩ x = x := by
  simp only [exten_prop, mem_inter, mem_enlarge, and_iff_right_iff_imp]
  intro u a
  simp_all only [true_or]

theorem repl_scheme (x : S) {n} (ψ : S → S → Prop)
    (f : BoundedFormula HF.Lang (Fin n) 2)  (qf : f.IsQF)
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
      Nat.succ_eq_add_one, realize_rel, mem_rel, Matrix.cons_val_zero, Term.realize_var,
      Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons, realize_ex, realize_inf, realize_bdEqual,
      realize_iff]
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

/-- The image of any set x under any definable mapping ψ is a set – {v : ∃ u ∈ x, ψ(u,v)}. -/
def setOfImage (x : S) (ψ : S → S → Prop) (n : ℕ)
    (f : BoundedFormula HF.Lang (Fin n) 2)  (qf : f.IsQF)
    (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) (h : (∀ u ∈ x, ∃! v, ψ u v)) : S
    := (repl_scheme x ψ f qf c hψ h).choose

@[simp] lemma mem_setOfImage (x v : S) (n : ℕ) (ψ : S → S → Prop)
    (f : BoundedFormula HF.Lang (Fin n) 2)  (qf : f.IsQF)
    (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) (h : (∀ u ∈ x, ∃! v, ψ u v)) :
    (v ∈ setOfImage x ψ n f qf c hψ h ↔ ∃ u ∈ x, ψ u v) := by
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
    let z := setOfImage Px (fun v u ↦ u = v ◁ y) 1 (&1 =' (.func ◁' ![&0, .var (.inl 0)]))
        (by refine IsAtomic.isQF ?_; exact
          IsAtomic.equal ((var ∘ Sum.inr) 1) (func ◁' ![(var ∘ Sum.inr) 0, var (Sum.inl 0)]))
        (![y]) (by simp) this
    use Px ∪ z
    intro u
    rw [exists_powerset_aux u x y Px hPx, mem_union, mem_setOfImage]
  | n => exact 0
  | f => exact ∃' ∀' ((&2 ∈' &1) ⇔ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &0))))
  | t => rename_i a; exact Fin.elim0 a
  | hP =>
    simp only [subset_def, Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_ex,
      Nat.succ_eq_add_one, realize_all, realize_iff, realize_rel, mem_rel, Matrix.cons_val_zero,
      Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons, realize_imp]
    rfl

/-- Power set. Defined through u ∈ powerset x ↔ u ⊆ x. -/
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
  | hP =>
    simp only [exists_prop, Nat.reduceAdd, Fin.isValue, Function.comp_apply, realize_imp,
      realize_all, Nat.succ_eq_add_one, realize_rel, mem_rel, Matrix.cons_val_zero,
      Term.realize_var, Sum.elim_inr, Matrix.cons_val_one, Matrix.head_cons, Sum.elim_inl,
      realize_ex, realize_inf, realize_not]
    rfl

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

end HFSet
