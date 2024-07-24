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

/-- Reverses all of the Fin-indexed variables of a term. -/
abbrev FirstOrder.Language.Term.reverse {L : Language} {α : Type u'} {n : ℕ} :
    L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin n)) :=
  relabel (Sum.map id (@Fin.rev n))

/-- Reverse first n variables, leave the rest. -/
def FirstOrder.Language.BoundedFormula.reverse_aux {L : Language} {α : Type u'} {n : ℕ} :
    ∀ (d : ℕ), L.BoundedFormula α (n + d) → L.BoundedFormula α (n + d)
  | _d, falsum => falsum
  | _d, equal t₁ t₂ => equal (t₁.reverse) (t₂.reverse)
  | _d, rel R ts => rel R fun i => (ts i).reverse
  | d, imp φ₁ φ₂ => (φ₁.reverse_aux d).imp (φ₂.reverse_aux d)
  | d, all φ => ((add_assoc n d 1 ▸ φ).reverse_aux (d + 1)).all

def FirstOrder.Language.BoundedFormula.reverse {L : Language} {α : Type u'} {n : ℕ} :
    L.BoundedFormula α n → L.BoundedFormula α n :=
  FirstOrder.Language.BoundedFormula.reverse_aux 0

--- this lemma might be true now
lemma realize_reverse {L : Language} {α : Type u'} {n : ℕ} [L.Structure S]
    (φ : BoundedFormula L α n) (v : α → S) (xs : Fin n → S) :
    φ.reverse.Realize v xs ↔ φ.Realize v (xs ∘ @Fin.rev n) := by
  unfold reverse reverse_aux
  induction' φ with m m t₁ t₂ m l R t m f₁ f₂ ih₁ ih₂ k f _
  · simp [Realize]
  · simp [Realize, Sum.elim_comp_map]
  · simp [Realize, Sum.elim_comp_map]
  · sorry
  · sorry


-- /-- Reverses all of the Fin-indexed variables of a formula. -/
-- abbrev FirstOrder.Language.BoundedFormula.reverse {L : Language} {α : Type u'} {n : ℕ}
--     (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
--   φ.mapTermRel (g := id) (fun _ t => t.reverse) (fun _ => id) (fun _ => castLE le_rfl)

-- lemma aux1 {L : Language} {α : Type u'} {m : ℕ} (f₁ f₂ : L.BoundedFormula α m)
--     (H : (f₁ ⟹ f₂).IsQF) : f₁.IsQF := by
--   rcases H with H|H|⟨H1, H2⟩
--   · rcases H with H|H
--   · exact H1

-- lemma aux2 {L : Language} {α : Type u'} {m : ℕ} (f₁ f₂ : L.BoundedFormula α m)
--     (H : (f₁ ⟹ f₂).IsQF) : f₂.IsQF := by
--   rcases H with H|H|⟨H1, H2⟩
--   · rcases H with H|H
--   · exact H2

-- @[simp] lemma realize_reverse_of_isQF {L : Language} [L.Structure S] {α : Type u'} {n : ℕ}
--     (φ : L.BoundedFormula α n) (hφ : φ.IsQF) {v : α → S} (xs : Fin n → S) :
--     φ.reverse.Realize v xs ↔ φ.Realize v (xs ∘ Fin.reverse n) := by
--   rw [reverse]
--   induction' φ with m m t₁ t₂ m l R t m f₁ f₂ ih₁ ih₂ k f _
--   · simp [mapTermRel, Realize]
--   · simp [mapTermRel, Realize, Sum.elim_comp_map]
--   · simp [mapTermRel, Realize, Sum.elim_comp_map]
--   · specialize ih₁ (aux1 f₁ f₂ hφ) xs
--     specialize ih₂ (aux2 f₁ f₂ hφ) xs
--     simp_all only [mapTermRel, Realize, id_eq]
--   · exfalso
--     exact not_all_isQF _ hφ

-- theorem repl_scheme (x : S) {n} (ψ : S → S → Prop)
--     (f : BoundedFormula HFLang (Fin n) 2)  (qf : f.IsQF)
--     (c : Fin n → S) (hψ : ∀ x y, ψ x y ↔ f.Realize c ![x, y]) :
--     (∀ u ∈ x, ∃ v, (ψ u v ∧ ∀ w, (ψ u w → w = v))) → (∃ (z : S), ∀ v, (v ∈ z ↔ ∃ u ∈ x, ψ u v)) := by
--   induction' x using HF.induction with x y hx _
--   · sorry -- done
--   · sorry -- done
--   · exact n
--   · exact
--       (∀' ((&1 ∈' &0) ⟹ ∃' (f.liftAt 1 0 /- f &1 &2 -/ ⊓ ∀' ((f.liftAt 1 0).liftAt 1 2 /- f &1 &3 -/ ⟹ &3 =' &2))))
--     ⟹ ∃' ∀' ((&2 ∈' &1) ⇔ ∃' ((&3 ∈' &0) ⊓ f.reverse.liftAt 2 0 /- f &3 &2-/))  -- should be correct
--   · rename_i a; exact c a
--   · simp
--     convert Iff.rfl
--     · rw [realize_liftAt (by norm_num), hψ]
--       convert Iff.rfl using 1
--       congr! 1
--       ext i
--       fin_cases i <;> simp <;> rfl
--     · rw [realize_liftAt (by norm_num), realize_liftAt (by norm_num), hψ]
--       convert Iff.rfl using 1
--       congr! 1
--       ext i
--       fin_cases i <;> simp <;> rfl
--     · rw [realize_liftAt (by norm_num), realize_reverse_of_isQF (hφ := qf), hψ]
--       rename_i h a b c
--       convert Iff.rfl using 1
--       congr! 1
--       ext i
--       fin_cases i <;> simp <;> rfl


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
