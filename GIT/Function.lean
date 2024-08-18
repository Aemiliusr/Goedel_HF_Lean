import GIT.Ordinal

open FirstOrder Language BoundedFormula Classical

/-!
# Appendix 3: P-functions

In this file, the third appendix of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness
Theorems' is formalised. It systematically presents the theory on (p-)functions and recursion
on ordinals for hereditarily finite sets.

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

suppress_compilation

variable {S : Type} [HF S]

namespace HF

/-- The set is a function, i.e. each element of the set is an ordered pair and it assigns exactly
one output to each input. Here 'input' and 'output' correspond to the first and second argument of
an ordered pair, respectively. -/
class IsFunc (f : S) : Prop :=
  pair_of_mem : (∀ y ∈ f, ∃ z z', y = pair z z')
  pair_unique : (∀ u v v', ((pair u v) ∈ f) → ((pair u v') ∈ f) → v = v')

namespace IsFunc

/-- The domain of a function f — {u ∈ ⋃₀ (⋃₀ f) : ∃ v, pair u v ∈ f}. -/
def dom (x : S) [IsFunc x] : S := setOfMem (⋃₀ (⋃₀ x)) (fun u ↦ ∃ v, (pair u v) ∈ x) 1
    (∃' (((.func ◁' ![((.func ◁' ![(.func ∅' Fin.elim0), (.func ◁' ![(.func ∅' Fin.elim0), &0])])),
    (.func ◁' ![(.func ◁' ![(.func ∅' Fin.elim0), &0]), &1])]))) ∈' (.var (.inl 0)))
    (![x]) (by simp [pair_eq, Fin.snoc])

@[simp] lemma mem_dom (x : S) [IsFunc x] (u : S) : u ∈ dom x ↔ ∃ v, pair u v ∈ x := by
  rw [dom, mem_setOfMem]
  simp only [mem_sUnion, and_iff_right_iff_imp, forall_exists_index]
  intros v h
  use {u, v}
  refine ⟨?_, by simp⟩
  use pair u v
  simpa

/-- The output of a function x given input u — the unique v such that pair u v ∈ x. -/
def apply (x : S) [IsFunc x] (u : S) : S :=
    if hu : u ∈ dom x then ((mem_dom x u).1 hu).choose else ∅

lemma apply_iff (x : S) [IsFunc x] (u : S) (hu : u ∈ dom x) (v : S) :
    apply x u = v ↔ pair u v ∈ x := by
  unfold apply; rw [dif_pos hu]
  refine ⟨?_, IsFunc.pair_unique _ _ _ ((mem_dom x u).1 hu).choose_spec⟩
  rintro rfl
  exact ((mem_dom x u).1 hu).choose_spec

end IsFunc

class IsSeq (s : S) (k : Ord S) [IsFunc s] : Prop :=
  dom_eq_ord : IsFunc.dom s = k.1
  dom_ne_emp : k ≠ ∅

namespace IsSeq

def apply (s : S) (k : Ord S) [IsFunc s] [IsSeq s k] (l : Ord S) : S :=
  if hl : l < k then ((IsFunc.mem_dom s l.1).1 (by
  rename_i seq
  rw [seq.1]
  simp [Ord.lt_iff] at hl
  exact hl)).choose else ∅

lemma apply_iff (s : S) (k : Ord S) [IsFunc s] [IsSeq s k] (l : Ord S) (hl : l < k) (y : S) :
    apply s k l = y ↔ pair l.1 y ∈ s := by
  unfold apply; rw [dif_pos hl]
  have : l.1 ∈ IsFunc.dom s := by
    rename_i seq
    rw [seq.1]
    simp [Ord.lt_iff] at hl
    exact hl
  refine ⟨?_, IsFunc.pair_unique _ _ _ ((IsFunc.mem_dom s l.1).1 this).choose_spec⟩
  rintro rfl
  exact ((IsFunc.mem_dom s l.1).1 this).choose_spec

end IsSeq

-- -- not correct for general n
-- abbrev IsFunctional (φ : S → S → Prop) (n : ℕ) (f : BoundedFormula HFLang (Fin n) 2)
--     (c : Fin n → S) (_hφ : ∀ x y, φ x y ↔ f.Realize c ![x, y]) (x : S) : Prop
--     := ∃! y, φ x y

-- -- not correct for general n
-- def pFunc (x : S) (φ : S → S → Prop) (n : ℕ) (f : BoundedFormula HFLang (Fin n) 2)
--     (c : Fin n → S) (hφ : ∀ x y, φ x y ↔ f.Realize c ![x, y]) (h : IsFunctional φ n f c hφ x) : S
--     := h.choose

abbrev IsFunctionalUnary (φ : S → S → Prop) (f : BoundedFormula HF.Lang (Fin 0) 2)
    (c : Fin 0 → S) (_hφ : ∀ x y, φ x y ↔ f.Realize c ![x, y]) (x : S) : Prop :=
    ∃! y, φ x y

abbrev IsFunctionalBinary (φ : S → S → S → Prop) (f : BoundedFormula HF.Lang (Fin 0) 3)
    (c : Fin 0 → S) (_hφ : ∀ x x' y, φ x x' y ↔ f.Realize c ![x, x', y]) (x x' : S) : Prop :=
    ∃! y, φ x x' y

abbrev IsFunctionalTernary (φ : S → S → S → S → Prop) (f : BoundedFormula HF.Lang (Fin 0) 4)
    (c : Fin 0 → S) (_hφ : ∀ x x' x'' y, φ x x' x'' y ↔ f.Realize c ![x, x', x'', y])
    (x x' x'' : S) : Prop := ∃! y, φ x x' x'' y

def pFuncUnary (x : S) (φ : S → S → Prop) (f : BoundedFormula HF.Lang (Fin 0) 2)
    (c : Fin 0 → S) (hφ : ∀ x y, φ x y ↔ f.Realize c ![x, y])
    (h : IsFunctionalUnary φ f c hφ x) : S :=
    h.choose

def pFuncBinary (x x' : S) (φ : S → S → S → Prop) (f : BoundedFormula HF.Lang (Fin 0) 3)
    (c : Fin 0 → S) (hφ : ∀ x x' y, φ x x' y ↔ f.Realize c ![x, x', y])
    (h : IsFunctionalBinary φ f c hφ x x') : S :=
    h.choose

def pFuncTernary (x x' x'' : S) (φ : S → S → S → S → Prop) (f : BoundedFormula HF.Lang (Fin 0) 4)
    (c : Fin 0 → S) (hφ : ∀ x x' x'' y, φ x x' x'' y ↔ f.Realize c ![x, x', x'', y])
    (h : IsFunctionalTernary φ f c hφ x x' x'') : S :=
    h.choose

lemma pFuncUnary_iff (x y : S) (φ : S → S → Prop) (f : BoundedFormula HF.Lang (Fin 0) 2)
    (c : Fin 0 → S) (hφ : ∀ x y, φ x y ↔ f.Realize c ![x, y]) (h : IsFunctionalUnary φ f c hφ x) :
    pFuncUnary x φ f c hφ h = y ↔ φ x y := by
  refine ⟨by rintro rfl; exact (h.choose_spec).1, ?_⟩
  rw [eq_comm]
  exact (h.choose_spec).2 y

lemma pFuncBinary_iff (x x' y : S) (φ : S → S → S → Prop) (f : BoundedFormula HF.Lang (Fin 0) 3)
    (c : Fin 0 → S) (hφ : ∀ x x' y, φ x x' y ↔ f.Realize c ![x, x', y])
    (h : IsFunctionalBinary φ f c hφ x x') : pFuncBinary x x' φ f c hφ h = y ↔ φ x x' y := by
  refine ⟨by rintro rfl; exact (h.choose_spec).1, ?_⟩
  rw [eq_comm]
  exact (h.choose_spec).2 y

lemma pFuncTernary_iff (x x' x'' y : S) (φ : S → S → S → S → Prop)
    (f : BoundedFormula HF.Lang (Fin 0) 4) (c : Fin 0 → S)
    (hφ : ∀ x x' x'' y, φ x x' x'' y ↔ f.Realize c ![x, x', x'', y])
    (h : IsFunctionalTernary φ f c hφ x x' x'') :
    pFuncTernary x x' x'' φ f c hφ h = y ↔ φ x x' x'' y := by
  refine ⟨by rintro rfl; exact (h.choose_spec).1, ?_⟩
  rw [eq_comm]
  exact (h.choose_spec).2 y

end HF
