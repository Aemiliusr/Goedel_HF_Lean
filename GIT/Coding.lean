import GIT.Model

open FirstOrder Language BoundedFormula

suppress_compilation

namespace HF

class inductive Γ0 (σ : C) where
| empty (h : σ = .func ∅' Fin.elim0) : Γ0 σ
| enlarge (h : ∃ τ, σ = .func ◁' ![τ, τ]) : Γ0 σ

example (σ : C) [Γ0 σ] : σ = .func ∅' Fin.elim0 ∨ ∃ τ, σ = .func ◁' ![τ, τ] := by
  rename_i inst
  match inst with
  | Γ0.empty h => left; exact h
  | Γ0.enlarge h => right; exact h

end HF
