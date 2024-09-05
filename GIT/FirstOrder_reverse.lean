import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

open FirstOrder Language BoundedFormula

/-!
# Reversing the variables of a term or formula

In this file, we define a function that reverses all of the Fin-indexed variables of a term or
a first-order formula. This is required for the proof of the replacement scheme.

## Main definitions
* `FirstOrder.Language.Term.reverse` : Reverses all of the Fin-indexed variables of a term.
* `FirstOrder.Language.BoundedFormula.reverse` : Reverses all of the Fin-indexed variables of a
  formula.

## Main statements
* `realize_reverse_of_isQF` : Similar to `FirstOrder.Language.BoundedFormula.realize_liftAt`but then
  for `reverse`.

## Implementation notes
* A notion of `realize_reverse` is only formalised for quantifier free formulas, as the
  quantifier-containing case caused problems.

## TO DO
* If necessary for formalising recursion on rank, formalize a notion of `realize_reverse` for
  quantifier-containing formulas.
-/

/-- Reverses all of the Fin-indexed variables of a term. -/
abbrev FirstOrder.Language.Term.reverse {L : Language} {α : Type u'} {n : ℕ} :
    L.Term (α ⊕ (Fin n)) → L.Term (α ⊕ (Fin n)) :=
  relabel (Sum.map id (@Fin.rev n))

/-- Reverses all of the Fin-indexed variables of a formula. -/
abbrev FirstOrder.Language.BoundedFormula.reverse {L : Language} {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormula α n) : L.BoundedFormula α n :=
  φ.mapTermRel (g := id) (fun _ t => t.reverse) (fun _ => id) (fun _ => castLE le_rfl)

lemma aux1 {L : Language} {α : Type u'} {m : ℕ} (f₁ f₂ : L.BoundedFormula α m)
    (H : (f₁ ⟹ f₂).IsQF) : f₁.IsQF := by
  rcases H with H|H|⟨H1, H2⟩
  · rcases H with H|H
  · exact H1

lemma aux2 {L : Language} {α : Type u'} {m : ℕ} (f₁ f₂ : L.BoundedFormula α m)
    (H : (f₁ ⟹ f₂).IsQF) : f₂.IsQF := by
  rcases H with H|H|⟨H1, H2⟩
  · rcases H with H|H
  · exact H2

/-- Similar to `FirstOrder.Language.BoundedFormula.realize_liftAt`but then for `reverse`. -/
@[simp] lemma realize_reverse_of_isQF {L : Language} [L.Structure S] {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormula α n) (hφ : φ.IsQF) {v : α → S} (xs : Fin n → S) :
    φ.reverse.Realize v xs ↔ φ.Realize v (xs ∘ @Fin.rev n) := by
  rw [reverse]
  induction' φ with m m t₁ t₂ m l R t m f₁ f₂ ih₁ ih₂ k f _
  · simp [mapTermRel, Realize]
  · simp [mapTermRel, Realize, Sum.elim_comp_map]
  · simp [mapTermRel, Realize, Sum.elim_comp_map]
  · specialize ih₁ (aux1 f₁ f₂ hφ) xs
    specialize ih₂ (aux2 f₁ f₂ hφ) xs
    simp_all only [mapTermRel, Realize, id_eq]
  · exfalso
    exact not_all_isQF _ hφ
