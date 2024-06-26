import Mathlib.Tactic
import GIT.app1
import GIT.app2
-- import LeanCopilot


open Classical

suppress_compilation

variable {S : Type u} [HF S]

namespace HF

def function (x : S) : Prop := (∀ y ∈ x, ∃ z z', y = ord_pair z z')
    ∧ (∀ u v v', ((ord_pair u v) ∈ x) → ((ord_pair u v') ∈ x) → v = v')

def dom (x : S) : S := pred_set (union_set (union_set x)) (fun u ↦ ∃ v, (ord_pair u v) ∈ x)

lemma exists_output_of_func (x y : S) (x_is_func : function x) (y_in_dom : y ∈ dom x) :
        ∃! z, ord_pair y z ∈ x := by
    rw [function] at x_is_func; cases' x_is_func with _ func2
    simp_rw [dom, pred_set_iff, union_set_iff] at y_in_dom
    rw [ExistsUnique]
    aesop

def output (x y : S) (x_is_func : function x) (y_in_dom : y ∈ dom x) : S :=
       (exists_output_of_func x y x_is_func y_in_dom).choose

lemma output_iff (x y : S) (x_is_func : function x) (y_in_dom : y ∈ dom x) :
        z = output x y x_is_func y_in_dom ↔ ord_pair y z ∈ x := by
    have := (exists_output_of_func x y x_is_func y_in_dom).choose_spec
    cases' this with h1 h2
    specialize h2 z; aesop

inductive ConstTerm : S → Prop
  | empty : ConstTerm (∅ : S)
  | enlarge {x y} (hx : ConstTerm x) (hy : ConstTerm y) : ConstTerm (x ◁ y)

-- theorem exists_function_for_const_term (t : S) (const_t : ConstTerm t)
--         (G : S → S) (H : S → S) : ∃ (F : S → S),
--         F = fun x => if eq_emp : x = ∅ then t else (if ord_x : ord x then G (F (predec x ord_x eq_emp)) else H x) := by
--     sorry

namespace ordinal

def Functional (φ : ordinal S → S → Prop) (k : ordinal S) : Prop := ∃! y, φ k y

def p_function (φ : ordinal S → S → Prop) (k : ordinal S) (hφ : Functional φ k) : S
        := (hφ).choose

def Seq (s : S) (k : ordinal S) : Prop := function s ∧ k ≠ ∅ ∧ dom s = k.1

lemma exists_output_of_Seq (s : S) (k l : ordinal S) (seq : Seq s k) (l_in_k : l ∈ k) :
        ∃! z, ord_pair l.1 z ∈ s := by
    rw [Seq] at seq; rcases seq with ⟨s_is_func, ⟨k_neq_emp, dom_is_k⟩⟩
    rw [mem, ← dom_is_k] at l_in_k
    exact exists_output_of_func s l.1 s_is_func l_in_k

def output_of_Seq (s : S) (k l : ordinal S) (seq : Seq s k) (l_in_k : l ∈ k) : S :=
        (exists_output_of_Seq s k l seq l_in_k).choose

lemma output_of_Seq_iff (s : S) (k l : ordinal S) (seq : Seq s k) (l_in_k : l ∈ k) :
        z = output_of_Seq s k l seq l_in_k ↔ ord_pair l.1 z ∈ s := by
    have := (exists_output_of_Seq s k l seq l_in_k).choose_spec
    cases' this with h1 h2
    specialize h2 z; aesop

-- def psi (k : ordinal S) (y : S) (G : S → S) : Prop := (k = ∅ ∧ y = ∅) ∨
--        (k ≠ ∅ ∧ ∃ (s : S), (Seq s k ∧ y = G  ))

theorem exists_recursive_function_on_ordinals_for_empty (G : S → S) :
        ∃ (F : ordinal S → S),
        F = fun k => if eq_emp : k = ∅ then ∅ else G (F (predec k eq_emp)) := by
    sorry

def recursive_function_on_ordinals_for_empty (G : S → S) : ordinal S → S :=
        (exists_recursive_function_on_ordinals_for_empty G).choose

lemma recursive_lemma1 (G : S → S) (k : ordinal S) (eq_emp : k = ∅) :
        recursive_function_on_ordinals_for_empty G k = ∅ := by
    have := (exists_recursive_function_on_ordinals_for_empty G).choose_spec
    rw [recursive_function_on_ordinals_for_empty, this]
    aesop

lemma recursive_lemma2 (G : S → S) (k : ordinal S) (neq_emp : k ≠ ∅) :
        recursive_function_on_ordinals_for_empty G k = G (recursive_function_on_ordinals_for_empty G (predec k neq_emp)) := by
    have := (exists_recursive_function_on_ordinals_for_empty G).choose_spec
    rw [recursive_function_on_ordinals_for_empty]
    sorry

end ordinal
end HF
