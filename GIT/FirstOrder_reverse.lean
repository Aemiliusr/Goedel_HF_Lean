import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

open FirstOrder Language BoundedFormula

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

@[simp] lemma realize_reverse_of_isQF {L : Language} [L.Structure S] {α : Type u'} {n : ℕ}
    (φ : L.BoundedFormula α n) (hφ : φ.IsQF) {v : α → S} (xs : Fin n → S) :
    φ.reverse.Realize v xs ↔ φ.Realize v (xs ∘ Fin.reverse n) := by
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
