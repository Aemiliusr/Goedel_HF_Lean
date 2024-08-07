import GIT.Ordinal

open FirstOrder Language BoundedFormula Classical

/-!
# Appendix 3: (P-)functions and recursion

In this file, the third appendix of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness
Theorems' is formalised. It systematically presents the theory on (p-)functions and recursion for
hereditarily finite sets.

## Main results

- `...`: ...

## Notation

- `◁` : enlarging, see `HFSet.enlarge`.
- `<` : less than (membership for the ordinal subtype), see `HFSet.Ord.lt`.
- `≤` : less than or equal to (membership or equality for the ordinal subtype), see `HFSet.Ord.le`.

## References

S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.
-/

local notation "∅'" => HFLang.emptySetSymbol

local notation " ◁' " => HFLang.enlargementSymbol

local notation t " ∈' " s => HFLang.membershipSymbol.boundedFormula ![t, s]

universe u

suppress_compilation

variable {S : Type u} [HFSet S]

namespace HFSet

/-- The set is a function, i.e. each element of the set is an ordered pair and it assigns exactly
one output to each input. Here 'input' and 'output' correspond to the first and second argument of
an ordered pair, respectively. -/
class IsFunc (f : S) : Prop :=
  pair_of_mem : (∀ y ∈ f, ∃ z z', y = pair z z')
  pair_unique : (∀ u v v', ((pair u v) ∈ f) → ((pair u v') ∈ f) → v = v')

namespace IsFunc

/-- The domain of a function f — {u ∈ ⋃₀ (⋃₀ f) : ∃ v, pair u v ∈ f}. -/
def dom (f : S) [IsFunc f] : S := setOfMem (⋃₀ (⋃₀ f)) (fun u ↦ ∃ v, (pair u v) ∈ f) 1
    (∃' (((.func ◁' ![((.func ◁' ![(.func ∅' Fin.elim0), (.func ◁' ![(.func ∅' Fin.elim0), &0])])),
    (.func ◁' ![(.func ◁' ![(.func ∅' Fin.elim0), &0]), &1])]))) ∈' (.var (.inl 0)))
    (![f]) (by simp [pair_eq, Fin.snoc])

@[simp] lemma mem_dom (f : S) [IsFunc f] (x : S) : x ∈ dom f ↔ ∃ y, pair x y ∈ f := by
  rw [dom, mem_setOfMem]
  simp only [mem_sUnion, and_iff_right_iff_imp, forall_exists_index]
  intros y h
  use {x, y}
  refine ⟨?_, by simp⟩
  use pair x y
  simpa

/-- The output of a function f given input x — the unique y such that pair x y ∈ f. -/
def apply (f : S) [IsFunc f] (x : S) : S :=
    if hx : x ∈ dom f then ((mem_dom f x).1 hx).choose else ∅

lemma apply_iff (f : S) [IsFunc f] (x : S) (hx : x ∈ dom f) (y : S) :
    apply f x = y ↔ pair x y ∈ f := by
  unfold apply; rw [dif_pos hx]
  refine ⟨?_, IsFunc.pair_unique _ _ _ ((mem_dom f x).1 hx).choose_spec⟩
  rintro rfl
  exact ((mem_dom f x).1 hx).choose_spec

end IsFunc

abbrev IsFunctional (φ : S → S → Prop) (n : ℕ) (f : BoundedFormula HFLang (Fin n) 2)
    (c : Fin n → S) (_hφ : ∀ x y, φ x y ↔ f.Realize c ![x, y]) (x : S) : Prop
    := ∃! y, φ x y

def p_function (x : S) (φ : S → S → Prop) (n : ℕ) (f : BoundedFormula HFLang (Fin n) 2)
    (c : Fin n → S) (hφ : ∀ x y, φ x y ↔ f.Realize c ![x, y]) (h : IsFunctional φ n f c hφ x) : S
    := h.choose

lemma p_function_iff (x y : S) (φ : S → S → Prop) (n : ℕ) (f : BoundedFormula HFLang (Fin n) 2)
    (c : Fin n → S) (hφ : ∀ x y, φ x y ↔ f.Realize c ![x, y]) (h : IsFunctional φ n f c hφ x) :
    p_function x φ n f c hφ h = y ↔ φ x y := by
  refine ⟨by rintro rfl; exact (h.choose_spec).1, ?_⟩
  rw [eq_comm]
  exact (h.choose_spec).2 y

end HFSet
