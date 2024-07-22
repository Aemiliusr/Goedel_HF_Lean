import Mathlib.Tactic
import GIT.app1
import GIT.app2
import GIT.app3

open Classical

suppress_compilation

variable {S : Type u} [HF S]

namespace HF
namespace ordinal

lemma power_injective : Function.Injective (PowerSet : S → S) := by
  rw [Function.Injective]
  intros s s' power_eq
  simp_rw [exten_prop, powerSet_iff, SubsetEq] at power_eq
  have power_eq' := power_eq
  specialize power_eq s; simp only [imp_self, implies_true, true_iff] at power_eq
  specialize power_eq' s'; simp only [imp_self, implies_true, iff_true] at power_eq'
  rw [exten_prop]
  aesop

def R : ordinal S → S := recursive_function_on_ordinals_for_empty PowerSet power_injective

lemma R_emp_eq_emp (k : ordinal S) (eq_emp : k = ∅) : R k = ∅ := by
    exact recursive_lemma1 PowerSet power_injective k eq_emp

lemma R_ord_eq_power (k : ordinal S) (neq_emp : k ≠ ∅) : R k = PowerSet (R (predec k neq_emp)) := by
    exact recursive_lemma2 PowerSet power_injective k neq_emp

lemma predec_R_subseteq_imp_R_subseteq (k l : ordinal S) (k_neq_emp : k ≠ ∅) (l_neq_emp : l ≠ ∅)
    (predec_subseteq : ∀ v ∈ R (predec k k_neq_emp), v ∈ R (predec l l_neq_emp)) : ∀ v ∈ R k, v ∈ R l := by
  rw [R_ord_eq_power k k_neq_emp]; rw [R_ord_eq_power l l_neq_emp]
  simp_rw [powerSet_iff, SubsetEq]
  aesop

theorem le_imp_R_subseteq (m n : ordinal S) (n_le_m : n ≤ m) : ∀ v ∈ (R n), v ∈ (R m)  := by
  by_cases eq_emp : n = ∅
  · simp_rw [R_emp_eq_emp n eq_emp, set_notin_empty, IsEmpty.forall_iff, implies_true]
  · by_contra n_not_subset
    have set_neq_emp : {k : ordinal S | k ≠ ∅ ∧ ∃ m, k ≤ m ∧ ¬ ∀ v ∈ (R k), v ∈ (R m)} ≠ ∅ := by
      rw [setOf]; by_contra
      have : ¬∃ (k : ordinal S), k ≠ ∅ ∧ ∃ m, k ≤ m ∧ ¬∀ v ∈ R k, v ∈ R m := by aesop
      apply this; use n
      refine ⟨by assumption, by use m⟩
    let k := min_set {k : ordinal S | k ≠ ∅ ∧ ∃ m, k ≤ m ∧ ¬ ∀ v ∈ (R k), v ∈ (R m)} set_neq_emp
    have k_in_set : k ∈ {k : ordinal S | k ≠ ∅ ∧ ∃ m, k ≤ m ∧ ¬ ∀ v ∈ (R k), v ∈ (R m)} := by apply min_set_in_set
    rcases k_in_set with ⟨k_neq_emp, ⟨m, ⟨k_le_m, k_not_subset⟩⟩⟩
    have predec_notin_set : predec k k_neq_emp ∉ {k : ordinal S | k ≠ ∅ ∧ ∃ m, k ≤ m ∧ ¬ ∀ v ∈ (R k), v ∈ (R m)} := by
      apply predec_of_min_set_notin_set {k : ordinal S | k ≠ ∅ ∧ ∃ m, k ≤ m ∧ ¬ ∀ v ∈ (R k), v ∈ (R m)} set_neq_emp k_neq_emp
    apply predec_notin_set
    have m_neq_emp : m ≠ ∅ := by
      by_contra!
      rw [this, le_iff, lt_iff] at k_le_m
      cases' k_le_m with k_in_emp k_eq_emp
      · apply set_in_empty_false k; assumption
      · apply k_neq_emp; assumption
    constructor
    · by_contra predec_eq_emp
      have predec_subset : ∀ v ∈ R (predec k k_neq_emp), v ∈ R (predec m m_neq_emp) := by
        rw [R_emp_eq_emp]; simp only [set_notin_empty, IsEmpty.forall_iff, implies_true]; assumption
      apply predec_R_subseteq_imp_R_subseteq at predec_subset
      apply k_not_subset; assumption
    · use predec m m_neq_emp
      constructor
      · cases' k_le_m with k_in_m k_eq_m
        · have := le_max m m_neq_emp; specialize this k k_in_m
          change k ≤ predec m m_neq_emp at this
          left; cases' this with k_in_predec k_eq_predec
          · apply predec_mem_aux; assumption
          · simp_rw [k_eq_predec]
            exact predec_mem (predec m m_neq_emp) (k_eq_predec ▸ k_neq_emp)
        · right; simp_rw [k_eq_m]
      · by_contra!
        apply predec_R_subseteq_imp_R_subseteq at this
        apply k_not_subset; assumption

theorem R_transitive (m : ordinal S) : tran (R m) := by
    simp_rw [tran]
    intros x x_in_Rm
    by_cases eq_emp : m = ∅
    · simp_rw [R_emp_eq_emp m eq_emp, set_notin_empty] at *
    · have predec_le : predec m eq_emp ≤ m := by have := predec_lt m eq_emp; rw [le_iff]; simp_all
      have R_subset := le_imp_R_subseteq m (predec m eq_emp) (predec_le)
      simp_rw [R_ord_eq_power m eq_emp, powerSet_iff, SubsetEq, powerSet_iff, SubsetEq] at *
      aesop

lemma exists_ordinal_set_in_R_aux (x y : S) (n m : ordinal S) (x_in_Rn : x ∈ R n) (y_in_Rm : y ∈ R m) :
        ∀ v ∈ x ◁ y, v ∈ Union (R n) (R (succ m)) := by
        simp_rw [enlarge_iff, union_iff]
        intros v h; cases' h with v_in_x v_eq_y
        · left
          apply R_transitive at x_in_Rn; rw [SubsetEq] at x_in_Rn
          specialize x_in_Rn v v_in_x
          exact x_in_Rn
        · right
          rw [R_ord_eq_power (succ m) (succ_neq_emp m), powerSet_iff, SubsetEq, predec_of_succ, v_eq_y]
          apply R_transitive at y_in_Rm; rwa [SubsetEq] at y_in_Rm

theorem exists_ordinal_set_in_R (x : S) : ∃ (n : ordinal S), x ∈ R n := by
    induction' x using HF.induction with x y hx hy
    · use succ ∅
      simp [R_ord_eq_power (succ ∅) (succ_neq_emp ∅), powerSet_iff, SubsetEq, predec_of_succ, R_emp_eq_emp]
    · cases' hx with n x_in_Rn; cases' hy with m y_in_Rm
      have h := exists_ordinal_set_in_R_aux x y n m x_in_Rn y_in_Rm
      simp_rw [union_iff] at h
      by_cases n_le_succ_m : n ≤ succ m
      · apply le_imp_R_subseteq (succ m) n at n_le_succ_m
        have xy_subseteq_Rsuccm : ∀ v ∈ x ◁ y, v ∈ R (succ m) := by intros v v_in_xy; specialize h v v_in_xy; aesop
        use succ (succ m)
        rw [R_ord_eq_power (succ (succ m)) (succ_neq_emp (succ m)), powerSet_iff, SubsetEq, predec_of_succ]
        exact xy_subseteq_Rsuccm
      · have succ_m_le_n : succ m ≤ n := by simp [le_iff, lt_iff] at *; have := exclusive_compar (succ m) n; aesop
        apply le_imp_R_subseteq n (succ m) at succ_m_le_n
        have xy_subseteq_Rn : ∀ v ∈ x ◁ y, v ∈ R n := by intros v v_in_xy; specialize h v v_in_xy; aesop
        use succ n
        rw [R_ord_eq_power (succ n) (succ_neq_emp n), powerSet_iff, SubsetEq, predec_of_succ]
        exact xy_subseteq_Rn
    · sorry
    · sorry
    · sorry
    · sorry

abbrev rank_set (x : S) : Set (ordinal S) := {n : ordinal S | x ∈ R (succ n)}

lemma rank_set_neq_emp (x : S) : rank_set x ≠ ∅ := by
  have := exists_ordinal_set_in_R x; cases' this with n hn
  simp_rw [rank_set, setOf]; by_contra
  have h : ¬∃ (n : ordinal S), x ∈ R (succ n) := by aesop
  apply h; use n
  apply le_imp_R_subseteq (succ n) n
  · have := succ_le_false n; push_neg at this
    rw [le_iff]; left; exact this
  · exact hn

lemma emp_in_rank_set_emp (x : S) (x_eq_emp : x = ∅) : (∅ : ordinal S) ∈ rank_set x  := by

  sorry

def rank (x : S) : ordinal S := min_set (rank_set x) (rank_set_neq_emp x)

lemma rank_eq_emp_iff_emp (x : S) : rank x = ∅ ↔ x = ∅ := by
  rw [rank]
  constructor
  · intro h

    sorry
  · intro h
    apply emp_in_rank_set_emp at h
    apply min_set_le (rank_set x) (rank_set_neq_emp x) ∅ at h
    rw [le_iff, lt_iff, set_in_empty_iff_false, false_or] at h
    assumption

lemma set_subset_of_R_rank (x : S) : ∀ v ∈ x, v ∈ R (rank x) := by
  intros v v_in_x
  sorry

theorem mem_imp_rank_lt (x y : S) (x_in_y : x ∈ y) : rank x < rank y := by
  sorry

end ordinal
end HF
