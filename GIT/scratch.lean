import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

open FirstOrder Language BoundedFormula

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

-- section Fin
-- variable {n : ℕ} {α : Fin (n + 1) → Type u} (x : α (last n)) (q : ∀ i, α i)
--    (p : ∀ i : Fin n, α (castSucc i)) (i : Fin n) (y : α (castSucc i)) (z : α (last n))

-- lemma Fin_snoc_zero' : Fin.snoc p s 0 = p 0 := sorry

-- end Fin
-- open Fin

----------------------------------------------------------------------------------------------------


/-- Comprehension Scheme -/
theorem comp_scheme (x : S) (φ : S → Prop) {n} (f : BoundedFormula HFLang (Fin n) 1) (c : Fin n → S)
    (hφ : ∀ x, φ x ↔ f.Realize c ![x]) : ∃ (z : S), ∀ (u : S), (u ∈ z ↔ u ∈ x ∧ φ u) := by
  induction' x using HF.induction with x w hx _
  · sorry -- done
  · sorry -- done
  · exact n
  · exact ∃' ∀' ((&2 ∈' &1) ⇔ ((&2 ∈' &0) ⊓ (f.liftAt 2 0)))
  · rename_i a; exact c a
  · simp
    convert Iff.rfl
    rw [realize_liftAt (by norm_num), hφ]
    convert Iff.rfl -- now aesop works
    simp_all only [Nat.reduceAdd, Fin.coe_fin_one, lt_self_iff_false, ↓reduceIte]
    ext1 x_2
    simp_all only [Matrix.cons_val_fin_one, Function.comp_apply]
    apply Eq.refl

/-- Subset that is defined by a formula φ — {u ∈ x : φ(u)} -/
noncomputable def SetByFormula (x : S) (φ : S → Prop) {n} (f : BoundedFormula HFLang (Fin n) 1) (c : Fin n → S)
    (hφ : ∀ x, φ x ↔ f.Realize c ![x]) : S := (comp_scheme x φ f c hφ).choose

lemma setByFormula_iff (x : S) (φ : S → Prop) {n} (f : BoundedFormula HFLang (Fin n) 1) (c : Fin n → S)
    (hφ : ∀ x, φ x ↔ f.Realize c ![x]) : ∀ (u : S), (u ∈ SetByFormula x φ f c hφ ↔ u ∈ x ∧ φ u) :=
  (comp_scheme x φ f c hφ).choose_spec

/-- x ∩ y = {u ∈ x : u ∈ y} -/
noncomputable def inter (x : S) (y : S) : S := sorry
    -- setByFormula x (fun u ↦ u ∈ y) _ _ _
    -- no clue what last arguments should be

lemma inter_iff (x y : S) : ∀ (u : S), (u ∈ inter x y ↔ u ∈ x ∧ u ∈ y) := by sorry
  -- exact setByFormula_iff _ _ _ _ _


/-- Auxiliary for reversing variables of a term. -/
abbrev Fin.reverse (n : ℕ) : Fin n → Fin n := fun x ↦ ⟨n - 1 - x.val, by
  cases n
  · exact x.elim0
  · omega
  ⟩

/-- Reverses all of the Fin-indexed variables of a term. -/
abbrev FirstOrder.Language.Term.reverse {L : Language} {α : Type u'} {n : ℕ} :
    L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin n)) :=
  relabel (Sum.map id (Fin.reverse n))

/-- Reverses all of the Fin-indexed variables of a formula. -/
abbrev FirstOrder.Language.BoundedFormula.reverse {L : Language} {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.mapTermRel (g := id) (fun _ t => t.reverse) (fun _ => id) (fun _ => castLE le_rfl)

lemma realize_reverse {n m} {φ : BoundedFormula HFLang (Fin n) m} {v : Fin n → S} {xs : Fin m → S} :
    (φ.reverse).Realize v xs ↔ (φ.Realize) v (xs ∘ Fin.reverse m) := by
  rw [reverse]
  induction' φ with _
  · simp [mapTermRel, Realize]
  · simp [mapTermRel, Realize, Sum.elim_comp_map]
  · simp [mapTermRel, Realize, Sum.elim_comp_map]
  · simp_all only [mapTermRel, Realize, id_eq]
  · sorry -- look at proof realize_liftAt

theorem repl_scheme (x : S) {n} (ψ : S → S → Prop) (f : BoundedFormula HFLang (Fin n) 2)
  (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) :
    (∀ u ∈ x, ∃ v, (ψ u v ∧ ∀ w, (ψ u w → w = v))) → (∃ (z : S), ∀ v, (v ∈ z ↔ ∃ u ∈ x, ψ u v)) := by
  induction' x using HF.induction with x y hx _
  · sorry -- done
  · sorry -- done
  · exact n
  · exact ∀' ((&1 ∈' &0) ⟹ ∃' (f.liftAt 1 0 /- f &1 &2 -/ ⊓ ∀' ((f.liftAt 1 0).liftAt 1 2 /- f &1 &3 -/ ⟹ &3 =' &2)))
    ⟹ ∃' ∀' ((&2 ∈' &1) ⇔ ∃' ((&3 ∈' &0) ⊓ (f.liftAt 2 0).reverse /- f &3 &2-/))  -- should be correct
  · rename_i a; exact c a
  · simp
    convert Iff.rfl
    · rw [realize_liftAt (by norm_num), hψ]
      convert Iff.rfl
      sorry
    · rw [realize_liftAt (by norm_num), realize_liftAt (by norm_num), hψ]
      convert Iff.rfl
      sorry
    · rw [realize_reverse, realize_liftAt (by norm_num), hψ]
      convert Iff.rfl
      sorry

lemma found_prop_lemma (x z : S) (h : ∀ w ∈ z, inter w z ≠ ∅) : x ∉ z ∧ inter x z = ∅ := by
  induction' x using HF.induction with x y hx hy
  · sorry -- done
  · sorry -- done
  · exact 1
  · sorry -- no clue how to incorporate 'inter'
  · exact z
  · sorry

----------------------------------------------------------------------------------------------------

/-- y ⊆ x -/
abbrev subset_eq (y x : S) : Prop := ∀ (v : S), v ∈ y → v ∈ x

/-- The set x is transitive -/
abbrev tran (x : S) : Prop := ∀ y ∈ x, subset_eq y x

/-- The set x is an ordinal -/
abbrev ord (x : S) : Prop := tran x ∧ ∀ y ∈ x, tran y

theorem exists_max_of_set_of_ord (x : S) (set_of_ord : ∀ k ∈ x, ord k) (neq_emp : x ≠ ∅) :
    ∃ l ∈ x, ∀ k ∈ x, (k ∈ l ∨ k = l) := by sorry
  -- induction' x using HF.induction with x y hx _

theorem exists_min_of_set_of_ord (x : S) (set_of_ord : ∀ k ∈ x, ord k) (neq_emp : x ≠ ∅) :
    ∃ l ∈ x, ∀ k ∈ x, (l ∈ k ∨ l = k) := by sorry
  -- induction' x using HF.induction with x y hx _

lemma toSetS_finite (x : S) : Set.Finite {s : S | s ∈ x} := by sorry
  -- induction' x using HF.induction with x y hx _


-- app4 also contains one occurence of HF.induction: `exists_ordinal_set_in_R `
