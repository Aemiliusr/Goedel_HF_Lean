import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Order

open FirstOrder Language BoundedFormula

/-- Reverses all of the Fin-indexed variables of a term. -/
abbrev FirstOrder.Language.Term.reverse {L : Language} {α : Type u'} {n : ℕ} :
    L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin n)) :=
  relabel (Sum.map id (@Fin.rev n))

-- abbrev FirstOrder.Language.Term.swap {L : Language} {α : Type u'} {n : ℕ} (i j : Fin n) :
--     L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin n)) :=
--   relabel (Sum.map id (fun x ↦ if x = i then j else if x = j then i else x : Fin n → Fin n))

/-- Reverse first n variables, leave the rest. -/
def FirstOrder.Language.BoundedFormula.reverse_aux {L : Language} {α : Type u'} {n : ℕ} :
    ∀ (d : ℕ), L.BoundedFormula α (n + d) → L.BoundedFormula α (n + d)
  | _d, falsum => falsum
  | _d, equal t₁ t₂ => equal (t₁.reverse) (t₂.reverse)
  | _d, rel R ts => rel R fun i => (ts i).reverse
  | d, imp φ₁ φ₂ => (φ₁.reverse_aux d).imp (φ₂.reverse_aux d)
  | d, all φ => ((add_assoc n d 1 ▸ φ).reverse_aux (d + 1)).all


-- -- /-- Reverse first n variables, leave the rest. -/
-- def FirstOrder.Language.BoundedFormula.swap_aux {L : Language} {α : Type u'} {n : ℕ} (i j : Fin n) :
--     ∀ (d : ℕ), L.BoundedFormula α (n + d) → L.BoundedFormula α (n + d)
--   | _d, falsum => falsum
--   | _d, equal t₁ t₂ =>
--     equal (t₁.swap (Fin.castLE (Nat.le_add_right n _d) i) (Fin.castLE (Nat.le_add_right n _d) j))
--       (t₂.swap (Fin.castLE (Nat.le_add_right n _d) i) (Fin.castLE (Nat.le_add_right n _d) j))
--   | _d, rel R ts => rel R fun x =>
--       (ts x).swap (Fin.castLE (Nat.le_add_right n _d) i) (Fin.castLE (Nat.le_add_right n _d) j)
--   | d, imp φ₁ φ₂ => (φ₁.swap_aux i j d).imp (φ₂.swap_aux i j d)
--   | d, all φ => ((add_assoc n d 1 ▸ φ).swap_aux i j (d + 1)).all

-- -- swap (∀ f) i j = ∀ swap f (i + 1) (j + 1)


variable {L : Language} {α : Type u'} in
def FirstOrder.Language.BoundedFormula.reverse {n : ℕ} :
    L.BoundedFormula α n → L.BoundedFormula α n :=
  FirstOrder.Language.BoundedFormula.reverse_aux 0


-- -- swap f i j = swap f j i
-- -- swap f i i = f
-- variable {L : Language} {α : Type u'} in
-- def FirstOrder.Language.BoundedFormula.swap {n : ℕ} (i j : Fin n) :
--     L.BoundedFormula α n → L.BoundedFormula α n :=
--   FirstOrder.Language.BoundedFormula.swap_aux i j 0


-- -- to prove for all i and j, we can assume j < i because if i = j, then swap doesn't change anything
-- -- if i < j then we can prove swap j i instead
-- -- can we assume i + 1 < n then?
-- -- if i + 1 = n, then we are dealing with swap f (n - 1) j = swap f j (n - 1) since j < i = n - 1
-- example {L : Language} {α : Type u'} {n : ℕ} (i j : Fin n) (hi : j < i) (hi' : i.1 + 1 < n)
--     (f : L.BoundedFormula α (n + 1)) :
--     (∀' f).swap i j =
--     -- if h : i.1 + 1 < n ∧ j < i then
--     ∀' (f.swap_aux ⟨i.1 + 1, by omega⟩ ⟨j.1 + 1, by omega⟩)
--     -- else
--     -- sorry
--     := by
--   -- suffices ....
--   induction' n with n ih
--   · simp only [not_lt_zero'] at hi'
--   ·
--     sorry

-- --- this lemma might be true now
-- lemma realize_swap {L : Language} {α : Type u'} {n : ℕ} (i j : Fin n) [L.Structure S]
--     (φ : BoundedFormula L α n) (v : α → S) (xs : Fin n → S) :
--     (φ.swap i j).Realize v xs ↔
--     φ.Realize v
--       (xs ∘ (fun x ↦ if x = i then j else if x = j then i else x : Fin n → Fin n)) := by
--   induction' φ with m m t₁ t₂ m l R t m f₁ f₂ ih₁ ih₂ k f ih
--   · unfold swap swap_aux
--     simp only [Realize]
--   · unfold swap swap_aux
--     simp only [Realize, Nat.add_zero, Fin.castLE_rfl, id_eq, Term.realize_relabel,
--       Sum.elim_comp_map, CompTriple.comp_eq]
--   · unfold swap swap_aux
--     simp only [Realize, Nat.add_zero, Fin.castLE_rfl, id_eq, Term.realize_relabel,
--       Sum.elim_comp_map, CompTriple.comp_eq]
--   · unfold swap swap_aux
--     simp only [Realize]
--     specialize ih₁ i j xs
--     specialize ih₂ i j xs
--     rw [← ih₁, ← ih₂]
--     unfold swap swap_aux
--     simp only [Nat.add_eq]
--   · simp only [realize_all, Nat.succ_eq_add_one]
--     unfold swap swap_aux
--     refine forall_congr' fun s => ?_
--     specialize ih (Fin.castLE (Nat.le_add_right k 1) i) (Fin.castLE (Nat.le_add_right k 1) j)
--       (Fin.snoc xs s)

--     have eq :
--       (Fin.snoc (xs ∘ fun x ↦ if x = i then j else if x = j then i else x) s : Fin (k + 1) → S) =
--       Fin.snoc xs s ∘ fun x ↦ if x = (Fin.castLE (Nat.le_add_right k 1) i)
--         then (Fin.castLE (Nat.le_add_right k 1) j)
--         else if x = (Fin.castLE (Nat.le_add_right k 1) j)
--         then (Fin.castLE (Nat.le_add_right k 1) i)
--         else x  := by
--       sorry
--     rw [eq, ← ih]
--     simp only [Nat.reduceAdd]
--     unfold swap swap_aux


--     sorry


--- this lemma might be true now
lemma realize_reverse {L : Language} {α : Type u'} {n : ℕ} [L.Structure S]
    (φ : BoundedFormula L α n) (v : α → S) (xs : Fin n → S) :
    φ.reverse.Realize v xs ↔ φ.Realize v (xs ∘ @Fin.rev n) := by
  -- unfold reverse reverse_aux
  induction' φ with m m t₁ t₂ m l R t m f₁ f₂ ih₁ ih₂ k f ih
  · unfold reverse reverse_aux
    simp [mapTermRel, Realize]
  · unfold reverse reverse_aux
    simp [mapTermRel, Realize, Sum.elim_comp_map]
  · unfold reverse reverse_aux
    simp [mapTermRel, Realize, Sum.elim_comp_map]
  · unfold reverse reverse_aux
    simp only [Nat.add_zero, realize_imp]
    specialize ih₁ xs
    specialize ih₂ xs
    rw [← ih₁, ← ih₂]
    unfold reverse reverse_aux
    simp only [Nat.add_eq]

  · simp only [realize_all, Nat.succ_eq_add_one]
    unfold reverse reverse_aux
    refine forall_congr' fun s => ?_
    have h₁ : (Fin.snoc (xs ∘ Fin.rev) s : Fin (k + 1) → S) =
       (Fin.cons s xs) ∘ Fin.rev := sorry
    specialize ih (Fin.cons s xs)
    rw [h₁, ← ih]

    conv_lhs => unfold reverse_aux

    sorry


lemma test : False := by
  let L := FirstOrder.Language.order
  letI : L.Structure ℕ := inferInstance
  let φ : L.BoundedFormula (Fin 0) 2 := Term.le (.var $ .inr 0) (.var $ .inr 1)
  let ψ := ∀' φ

  have h1 : ¬ ψ.reverse.Realize finZeroElim ![0] := by
    unfold reverse reverse_aux
    simp only [Nat.add_eq, Nat.add_zero, Nat.reduceAdd, realize_all, Nat.succ_eq_add_one,
      not_forall]
    use 1
    rw [show Fin.snoc ![0] 1 = ![0, 1] by
      ext i; fin_cases i
      · simp [Fin.snoc]
      · rfl]
    simp only [Term.reverse, Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd]
    unfold reverse_aux
    simp only [Realize, Nat.reduceAdd, Fin.isValue, Term.realize_relabel]
    set x := _; change ¬ Structure.RelMap _ x
    have eq1 : x = ![1, 0] := by
      simp only [Fin.isValue, Nat.succ_eq_add_one, Nat.reduceAdd, x]
      ext i
      fin_cases i
      · simp only [Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero, Term.realize_var,
        Function.comp_apply, Sum.map_inr, Fin.rev_zero, Sum.elim_inr]; rfl
      · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons,
        Term.realize_var, Function.comp_apply, Sum.map_inr, Sum.elim_inr]; rfl
    rw [eq1]
    rw [relMap_leSymb]
    omega

  have h2 : ψ.Realize finZeroElim ![0] := by
    simp only [Fin.isValue, realize_all, Nat.succ_eq_add_one, Nat.reduceAdd, Term.realize_le,
      Term.realize_var, Sum.elim_inr, ψ, φ]
    intro n
    simp only [Fin.snoc, Nat.reduceAdd, Fin.isValue, Fin.val_zero, zero_lt_one, ↓reduceDIte,
      Nat.zero_eq, Fin.castSucc_castLT, Matrix.cons_val_fin_one, cast_eq, Fin.val_one,
      lt_self_iff_false, zero_le]


  rw [realize_reverse (φ := ψ) finZeroElim] at h1
  exact h1 (by convert h2; ext; simp)
