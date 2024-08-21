import GIT.Model

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

inductive IsInΓ0 : C → Prop where
| empty (h : σ = .func ∅' Fin.elim0) : IsInΓ0 σ
| enlarge (τ : C) (hτ : IsInΓ0 τ) : IsInΓ0 (.func ◁' ![τ, τ])

example (σ : C) (hσ : IsInΓ0 σ) : σ = .func ∅' Fin.elim0 ∨ ∃ τ, σ = .func ◁' ![τ, τ] := by
  match hσ with
  | .empty h => left; exact h
  | .enlarge τ hτ => right; exact ⟨τ, rfl⟩

inductive IsInΓ : C → Prop where
| isInΓ0 (h : IsInΓ0 σ) : IsInΓ σ
| pair (τ₁ τ₂ : C) (hτ₁ : IsInΓ τ₁) (hτ₂ : IsInΓ τ₂) :
    IsInΓ (.func ◁' ![(.func ◁' ![.func ∅' Fin.elim0, .func ◁' ![.func ∅' Fin.elim0, τ₁] ]),.func ◁' ![.func ◁' ![.func ∅' Fin.elim0, τ₁] ,τ₂] ])

variable (c : C)
def code : Lang.Formula α → C
| .falsum => .func ∅' Fin.elim0
| .equal t₁ t₂ => sorry -- whatever the code for t1 = t2 is
| .all _ => sorry
| .imp φ ψ => sorry
| .rel φ ψ => sorry

end HF
