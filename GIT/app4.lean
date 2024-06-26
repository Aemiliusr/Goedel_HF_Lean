import Mathlib.Tactic
import GIT.app1
import GIT.app2
import GIT.app3

open Classical

suppress_compilation

variable {S : Type u} [HF S]

namespace HF
namespace ordinal

def R : ordinal S → S := recursive_function_on_ordinals_for_empty power

lemma R_emp_eq_emp (k : ordinal S) (eq_emp : k = ∅) : R k = ∅ := by
    exact recursive_lemma1 power k eq_emp

lemma R_ord_eq_power (k : ordinal S) (neq_emp : k ≠ ∅) : R k = power (R (predec k neq_emp)) := by
    exact recursive_lemma2 power k neq_emp

theorem le_imp_R_subseteq (m n : ordinal S) (n_le_m : n ≤ m) : ∀ v ∈ (R n), v ∈ (R m)  := by
  by_cases eq_emp : n = ∅
  · simp_rw [R_emp_eq_emp n eq_emp, set_notin_empty, IsEmpty.forall_iff, implies_true]
  · by_contra n_not_subset
    have set_neq_emp : {k : ordinal S | k ≠ ∅ ∧ k ≤ m ∧ ¬ ∀ v ∈ (R k), v ∈ (R m)} ≠ ∅ := by
      rw [setOf]; by_contra
      have h : ¬∃ (k : ordinal S), k ≠ ∅ ∧ k ≤ m ∧ ¬∀ v ∈ R k, v ∈ R m := by aesop
      apply h; use n
    let k := min_set {k | k ≠ ∅ ∧ k ≤ m ∧ ¬∀ v ∈ R k, v ∈ R m} set_neq_emp
    have k_in_set : k ∈ {k | k ≠ ∅ ∧ k ≤ m ∧ ¬∀ v ∈ R k, v ∈ R m} := by apply min_set_in_set
    rcases k_in_set with ⟨k_neq_emp, ⟨k_le_m, k_not_subset⟩⟩
    have m_neq_emp : m ≠ ∅ := by
      by_contra!
      rw [this, le_iff, lt_iff] at n_le_m
      have := set_in_empty_false n; aesop
    have predec_k_le_m : predec k k_neq_emp ≤ m := by
      sorry
    have predec_le : predec k k_neq_emp ≤ predec m m_neq_emp := by
      sorry
    have predec_notin_set : predec k k_neq_emp ∉ {k : ordinal S | k ≠ ∅ ∧ k ≤ m ∧ ¬ ∀ v ∈ (R k), v ∈ (R m)} := by
      have := predec_of_min_set_notin_set {k : ordinal S | k ≠ ∅ ∧ k ≤ m ∧ ¬ ∀ v ∈ (R k), v ∈ (R m)} set_neq_emp k_neq_emp
      aesop
    have h : predec k k_neq_emp = ∅ ∨ ∀ v ∈ R (predec k k_neq_emp), v ∈ R m := by
      sorry
    cases' h with h1 h2
    · sorry
    · sorry

theorem R_transitive (m : ordinal S) : tran (R m) := by
    simp_rw [tran]
    intros x x_in_Rm
    by_cases eq_emp : m = ∅
    · simp_rw [R_emp_eq_emp m eq_emp, set_notin_empty] at *
    · have predec_le : predec m eq_emp ≤ m := by have := predec_lt m eq_emp; rw [le_iff]; simp_all
      have R_subset := le_imp_R_subseteq m (predec m eq_emp) (predec_le)
      simp_rw [R_ord_eq_power m eq_emp, power_iff, subset_eq, power_iff, subset_eq] at *
      aesop

lemma exists_ordinal_set_in_R_aux (x y : S) (n m : ordinal S) (x_in_Rn : x ∈ R n) (y_in_Rm : y ∈ R m) :
        ∀ v ∈ x ◁ y, v ∈ union (R n) (R (succ m)) := by
        simp_rw [enlarge_iff, union_iff]
        intros v h; cases' h with v_in_x v_eq_y
        · left
          apply R_transitive at x_in_Rn; rw [subset_eq] at x_in_Rn
          specialize x_in_Rn v v_in_x
          exact x_in_Rn
        · right
          rw [R_ord_eq_power (succ m) (succ_neq_emp m), power_iff, subset_eq, predec_of_succ, v_eq_y]
          apply R_transitive at y_in_Rm; rwa [subset_eq] at y_in_Rm

theorem exists_ordinal_set_in_R (x : S) : ∃ (n : ordinal S), x ∈ R n := by
    induction' x using HF.induction with x y hx hy
    · use succ ∅
      simp [R_ord_eq_power (succ ∅) (succ_neq_emp ∅), power_iff, subset_eq, predec_of_succ, R_emp_eq_emp]
    · cases' hx with n x_in_Rn; cases' hy with m y_in_Rm
      have h := exists_ordinal_set_in_R_aux x y n m x_in_Rn y_in_Rm
      simp_rw [union_iff] at h
      by_cases n_le_succ_m : n ≤ succ m
      · apply le_imp_R_subseteq (succ m) n at n_le_succ_m
        have xy_subseteq_Rsuccm : ∀ v ∈ x ◁ y, v ∈ R (succ m) := by intros v v_in_xy; specialize h v v_in_xy; aesop
        use succ (succ m)
        rw [R_ord_eq_power (succ (succ m)) (succ_neq_emp (succ m)), power_iff, subset_eq, predec_of_succ]
        exact xy_subseteq_Rsuccm
      · have succ_m_le_n : succ m ≤ n := by simp [le_iff, lt_iff] at *; have := exclusive_compar (succ m) n; aesop
        apply le_imp_R_subseteq n (succ m) at succ_m_le_n
        have xy_subseteq_Rn : ∀ v ∈ x ◁ y, v ∈ R n := by intros v v_in_xy; specialize h v v_in_xy; aesop
        use succ n
        rw [R_ord_eq_power (succ n) (succ_neq_emp n), power_iff, subset_eq, predec_of_succ]
        exact xy_subseteq_Rn

def rank_set (x : S) : Set (ordinal S) := {n : ordinal S | x ∈ R (succ n)}

lemma rank_set_neq_emp (x : S) : rank_set x ≠ ∅ := by
  have := exists_ordinal_set_in_R x; cases' this with n hn
  simp_rw [rank_set, setOf]; by_contra
  have h : ¬∃ (n : ordinal S), x ∈ R (succ n) := by aesop
  apply h; use n
  apply le_imp_R_subseteq (succ n) n
  · have := succ_le_false n; push_neg at this
    rw [le_iff]; left; exact this
  · exact hn

def rank (x : S) : ordinal S := min_set (rank_set x) (rank_set_neq_emp x)

lemma set_subset_of_R_rank (x : S) : ∀ v ∈ x, v ∈ R (rank x) := by

  sorry

theorem mem_imp_rank_lt (x y : S) (x_in_y : x ∈ y) : rank x < rank y := by
  sorry

end ordinal
end HF
