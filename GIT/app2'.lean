import Mathlib.Tactic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import GIT.app1

open Classical FirstOrder Language BoundedFormula

/-!
# Appendix 2: Ordinals of hereditarily finite set theory

In this file, Appendix 2 of S. Swierczkowski: 'Finite Sets and Gödel’s Incompleteness Theorems' is formalised.
It presents the theory on hereditarily finite ordinals.

This work contains a stronger version of the original Theorem 2.7 on the ordering of ordinals. See section 'On the ordering of ordinals'.

By 'set' we mean an 'HF set'; by 'collection' we mean a 'Lean set' (i.e. a set which need not be HF).

## Main results

- `HF.compar_of_ord_ord`: Comparability of ordinals.
- `HF.exists_max_of_set_of_ord`: Existence of a largest element of a set of ordinals.
- `HF.exists_min_of_set_of_ord`: Existence of a smallest element of a set of ordinals.
- `HF.ordinal.lt_wf`: The binary relation < is well-founded on every collection of ordinals.
- `HF.ordinal.exists_min_set`: Existence of a smallest element of a collection of ordinals.
- `HF.ordinal.cond_comp_lin_ord_bot`: The ordinals, ordered by <, form a conditionally complete linear order with a bottom element.

## Notation

- `◁` : enlarging, see `HF.enlarge`.
- `<` : membership for ordinals. See section 'On the ordering of ordinals'.
- `≤` : membership or equality for ordinals. See section 'On the ordering of ordinals'.

## References

S. Swierczkowski. Finite Sets and Gödel’s Incompleteness Theorems. Dissertationes
mathematicae. IM PAN, 2003. URL https://books.google.co.uk/books?id=5BQZAQAAIAAJ.
-/

local notation t " ∈' " s => HFLang.membershipSymbol.boundedFormula ![t, s]

suppress_compilation

variable {S : Type u} [HF S]

namespace HF

/-- The set is transitive. -/
abbrev IsTrans (x : S) : Prop := ∀ y ∈ x, SubsetEq y x

lemma isTrans_mem (x y z : S) (trans : IsTrans x) (y_in_x : y ∈ x) (z_in_y : z ∈ y) :
    z ∈ x := by apply trans <;> assumption

/-- The set is an ordinal. -/
abbrev IsOrd (x : S) : Prop := IsTrans x ∧ ∀ y ∈ x, IsTrans y

lemma mem_of_ord_isOrd (x y : S) (ord : IsOrd x) (y_in_x : y ∈ x) : IsOrd y := by
  refine ⟨ord.2 y y_in_x, ?_⟩
  intros z z_in_y
  apply ord.2
  exact isTrans_mem x y z ord.1 y_in_x z_in_y

lemma false_if_isOrd_and_mutual_mem (k l : S) (ord_k : IsOrd k) (k_in_l : k ∈ l) (l_in_k : l ∈ k) : False := by
  apply ord_k.1 l l_in_k at k_in_l
  rwa [← set_in_itself_iff_false k]

lemma empty_isOrd : IsOrd (∅ : S) := by unfold IsOrd IsTrans; simp_all

lemma empty_if_in_ord_and_disjoint (x w : S) (ord : IsOrd x) (w_in_x : w ∈ x)
    (disj : Inter w x = ∅) : w = ∅ := by
  simp only [exten_prop, inter_iff, set_in_empty_iff_false, iff_false, not_and] at disj
  apply ord.1 at w_in_x
  rw [HF.empty]
  simp_all

lemma empty_in_ord (x : S) (ord : IsOrd x) (neq_emp : x ≠ ∅) : ∅ ∈ x := by
  obtain ⟨w, ⟨w_in_x, disj⟩⟩ := found_prop x neq_emp
  apply empty_if_in_ord_and_disjoint x w ord w_in_x at disj
  subst w; assumption

/-- The successor of a set. -/
abbrev Succ (x : S) : S := x ◁ x

lemma succ_isOrd_if_isOrd (x : S) (ord : IsOrd x) : IsOrd (Succ x) := by
  unfold IsOrd IsTrans Succ SubsetEq
  simp only [enlarge_iff]
  constructor
  · intros y h v v_in_y
    left
    cases' h with y_in_x y_eq_x
    · exact isTrans_mem x y v ord.1 y_in_x v_in_y
    · rwa [← y_eq_x]
  · intros y h z z_in_y v v_in_z
    cases' h with y_in_x y_eq_x
    · apply mem_of_ord_isOrd x y ord at y_in_x
      exact isTrans_mem y z v y_in_x.1 z_in_y v_in_z
    · subst y
      exact isTrans_mem x z v ord.1 z_in_y v_in_z

lemma succ_isOrd_iff_isOrd (x : S) : IsOrd (Succ x) ↔ IsOrd x := by
  refine ⟨?_, succ_isOrd_if_isOrd x⟩
  intro h
  exact mem_of_ord_isOrd (Succ x) x h (by simp)

lemma succ_of_ord_notin_ord (k : S) (ord : IsOrd k) : Succ k ∉ k := by
  intro succ_k_in_k
  apply ord.1 (Succ k) at succ_k_in_k
  specialize succ_k_in_k k (by simp only [enlarge_iff, set_in_itself_iff_false, or_true])
  rwa [← set_in_itself_iff_false k]

lemma compar_of_ord_ord_aux1 (h : ∃ (k l : S), IsOrd k ∧ IsOrd l ∧ k ∉ l ∧ k ≠ l ∧ l ∉ k) :
    ∃ (k0 : S), IsOrd k0 ∧ (∀ m ∈ k0, ∀ l, IsOrd l → (m ∈ l ∨ m = l ∨ l ∈ m))
    ∧ (∃ l, IsOrd l ∧ (k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0)) := by
  rcases h with ⟨k, ⟨l, ⟨ord_k, ⟨ord_l, hkl⟩⟩⟩⟩
  -- have (k0 : S) : IsOrd k0 ∧ ∃ l, IsOrd l ∧ (k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0) := by sorry
  -- unfold IsOrd IsTrans SubsetEq at h
  let K := SetByFormula (n := 0) (PowerSet k)
    (fun k0 ↦ (((∀ y ∈ k0, ∀ v ∈ y, v ∈ k0) ∧ (∀ y ∈ k0, ∀ y_1 ∈ y, ∀ v ∈ y_1, v ∈ y)) ∧
    ∃ l, ((∀ y ∈ l, ∀ v ∈ y, v ∈ l) ∧ ∀ y ∈ l, ∀ y_1 ∈ y, ∀ v ∈ y_1, v ∈ y) ∧ k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0))
    (((∀' ((&1 ∈' &0) ⟹ (∀' ((&2 ∈' &1) ⟹ (&2 ∈' &0)))))
    ⊓ (∀' ((&1 ∈' &0) ⟹ (∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &1))))))))
    ⊓ (∃' (((∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &1)))))
    ⊓ (∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (∀' ((&4 ∈' &3) ⟹ (&4 ∈' &2))))))))
    ⊓ ((∼(&0 ∈' &1)) ⊓ (∼(&0 =' &1)) ⊓  (∼(&1 ∈' &0))))))
    (![]) (by simp [Fin.snoc]; sorry)
  have K_neq_emp : K ≠ ∅ := by
    rw [set_neq_empty_iff_exists_mem]
    use k
    rw [setByFormula_iff, powerSet_iff, SubsetEq]
    refine ⟨by simp, ⟨by assumption, by use l⟩⟩
  obtain ⟨k0, ⟨k0_in_K, k0_K_disj⟩⟩ := found_prop K K_neq_emp
  rw [setByFormula_iff] at k0_in_K
  rcases k0_in_K with ⟨k0_power_k, ⟨ord_k0, hk0⟩⟩
  refine ⟨k0, by exact ord_k0, ⟨?_, by exact hk0⟩⟩
  by_contra! hn
  rcases hn with ⟨r0, ⟨r0_in_k0, ⟨l0, ⟨ord_l0, hr0l0⟩⟩⟩⟩
  simp only [empty, inter_iff] at k0_K_disj
  refine k0_K_disj r0 ⟨r0_in_k0, ?_⟩
  rw [setByFormula_iff, powerSet_iff] at *
  have r0_in_k : r0 ∈ k := by simp_all
  apply ord_k.1 at r0_in_k
  refine ⟨r0_in_k, ⟨mem_of_ord_isOrd k0 r0 ord_k0 r0_in_k0, ⟨l0, ⟨ord_l0, hr0l0⟩⟩⟩⟩

lemma compar_of_ord_ord_aux2 (k0 : S) (h : ∃ (l : S), IsOrd l ∧ k0 ∉ l ∧ k0 ≠ l ∧ l ∉ k0) :
    ∃ (l0 : S), IsOrd l0 ∧ (∀ p ∈ l0, k0 ∈ p ∨ k0 = p ∨ p ∈ k0)
    ∧ (k0 ∉ l0 ∧ k0 ≠ l0 ∧ l0 ∉ k0) := by
  rcases h with ⟨l, ⟨ord_l, hk0l⟩⟩
  -- have (l0 : S) : IsOrd l0 ∧ (k0 ∉ l0 ∧ k0 ≠ l0 ∧ l0 ∉ k0) := by sorry
  -- unfold IsOrd IsTrans SubsetEq at h
  let L := SetByFormula (n := 1) (PowerSet l)
    (fun l0 ↦ ((∀ y ∈ l0, ∀ v ∈ y, v ∈ l0) ∧ (∀ y ∈ l0, ∀ y_1 ∈ y, ∀ v ∈ y_1, v ∈ y) ∧ (k0 ∉ l0) ∧ (k0 ≠ l0) ∧ (l0 ∉ k0)))
    ((∀' ((&1 ∈' &0) ⟹ (∀' ((&2 ∈' &1) ⟹ (&2 ∈' &0)))))
    ⊓ (∀' ((&1 ∈' &0) ⟹ (∀' ((&2 ∈' &1) ⟹ (∀' ((&3 ∈' &2) ⟹ (&3 ∈' &1)))))))
    ⊓ (∼((.var (.inl 0)) ∈' &0)) ⊓ (∼((.var (.inl 0)) =' &0)) ⊓ (∼(&0 ∈' (.var (.inl 0)))))
    (![k0]) (by simp [Fin.snoc]; sorry)
  have L_neq_emp : L ≠ ∅ := by
    rw [set_neq_empty_iff_exists_mem]
    use l
    rw [setByFormula_iff, powerSet_iff, SubsetEq]
    refine ⟨by simp, ⟨ord_l.1, ⟨ord_l.2, hk0l⟩⟩⟩
  obtain ⟨l0, ⟨l0_in_L, l0_L_disj⟩⟩ := found_prop L L_neq_emp
  rw [setByFormula_iff] at l0_in_L
  rcases l0_in_L with ⟨l0_power_l, ⟨ord_l0_1, ⟨ord_l0_2, hk0l0⟩⟩⟩
  refine ⟨l0, ⟨ord_l0_1, ord_l0_2⟩, ⟨?_, by exact hk0l0⟩⟩
  by_contra! hn
  rcases hn with ⟨q0, ⟨q0_in_l0, hk0q0⟩⟩
  simp only [empty, inter_iff] at l0_L_disj
  refine l0_L_disj q0 ⟨q0_in_l0, ?_⟩
  rw [setByFormula_iff, powerSet_iff] at *
  have q0_in_l : q0 ∈ l := by simp_all
  apply ord_l.1 at q0_in_l
  apply mem_of_ord_isOrd l0 q0 (by refine ⟨ord_l0_1, ord_l0_2⟩) at q0_in_l0
  refine ⟨q0_in_l, ⟨q0_in_l0.1, ⟨q0_in_l0.2, hk0q0⟩⟩⟩

lemma compar_of_ord_ord_aux3 (k0 l0 : S) (ord_l0 : IsOrd l0) (forall_in_l0 : ∀ p ∈ l0, k0 ∈ p ∨ k0 = p ∨ p ∈ k0)
    (hl0 : k0 ∉ l0 ∧ k0 ≠ l0 ∧ l0 ∉ k0) : Subset l0 k0 := by
  refine ⟨?_, by intro a; subst a; simp_all only [and_imp, or_true, implies_true, ne_eq,
    set_in_itself_iff_false, not_false_eq_true, not_true_eq_false, and_true, and_false]⟩
  intros p p_in_l0
  specialize forall_in_l0 p p_in_l0
  rcases forall_in_l0 with k0_in_p | k0_eq_p | p_in_k0
  · apply ord_l0.1 at p_in_l0
    specialize p_in_l0 k0 k0_in_p
    exfalso; apply hl0.1
    assumption
  · subst p
    exfalso; apply hl0.1
    assumption
  · assumption

theorem compar_of_ord_ord (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) :
    k ∈ l ∨ k = l ∨ l ∈ k := by
  revert k l
  by_contra! hn
  obtain ⟨k0, ⟨ord_k0, ⟨forall_in_k0, hk0⟩⟩⟩ := compar_of_ord_ord_aux1 hn
  obtain ⟨l0, ⟨ord_l0, ⟨forall_in_l0, hl0⟩⟩⟩ := compar_of_ord_ord_aux2 k0 hk0
  obtain ⟨m, ⟨m_in_k0 , m_notin_l0⟩⟩ := exists_set_notin_inter_if_subset l0 k0 (compar_of_ord_ord_aux3 k0 l0 ord_l0 forall_in_l0 hl0)
  specialize forall_in_k0 m m_in_k0 l0 ord_l0
  simp only [m_notin_l0, false_or] at forall_in_k0
  cases' forall_in_k0 with m_eq_l0 l0_in_m
  · simp_all
  · unfold IsOrd IsTrans SubsetEq at ord_k0
    apply ord_k0.1 m m_in_k0 at l0_in_m
    simp_all

theorem exclusive_compar_of_ord_ord (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) :
  (k ∈ l ∧ (k ≠ l ∧ l ∉ k)) ∨ (k = l ∧ (k ∉ l ∧ l ∉ k)) ∨ (l ∈ k ∧ (k ∉ l ∧ k ≠ l)) := by
  by_cases k_in_l : k ∈ l
  · left
    refine ⟨k_in_l, ⟨neq_if_mem k l k_in_l, ?_⟩⟩
    by_contra l_in_k
    apply false_if_isOrd_and_mutual_mem k l ord_k k_in_l l_in_k
  · by_cases k_eq_l : k = l
    · right; left
      refine ⟨k_eq_l, ⟨k_in_l, by subst k; exact k_in_l⟩⟩
    · right; right
      apply compar_of_ord_ord k l ord_k at ord_l
      simp only [k_in_l, not_false_eq_true, k_eq_l, false_or, ne_eq, and_self, and_true] at *
      exact ord_l

@[simp] lemma subset_iff_mem_if_isOrd_isOrd (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) :
    Subset k l ↔ k ∈ l := by
  constructor
  · intro k_subset_l
    apply compar_of_ord_ord k l ord_k at ord_l
    simp only [k_subset_l.2, false_or] at ord_l
    cases' ord_l with k_in_l l_in_k; exact k_in_l
    apply k_subset_l.1 at l_in_k
    exfalso; rwa [← set_in_itself_iff_false l]
  · intro k_in_l
    refine ⟨by apply ord_l.1; exact k_in_l, neq_if_mem k l k_in_l⟩

lemma succ_eq_or_succ_in_if_mem (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) (l_in_k : l ∈ k)  :
  Succ l = k ∨ Succ l ∈ k := by
  have h := compar_of_ord_ord k (Succ l) ord_k (succ_isOrd_if_isOrd l ord_l)
  cases' h with k_in_succ_l h
  · simp only [enlarge_iff] at k_in_succ_l
    cases' k_in_succ_l with k_in_l k_eq_l
    · exfalso; apply false_if_isOrd_and_mutual_mem k l ord_k k_in_l l_in_k
    · exfalso; apply neq_if_mem l k l_in_k; rw [k_eq_l]
  · rwa [eq_comm]

lemma eq_if_succ_eq_if_isOrd_isOrd (k l : S) (ord_k : IsOrd k) (ord_l : IsOrd l) (succ_eq : Succ k = Succ l) :
    k = l := by
  by_contra! k_neq_l
  apply compar_of_ord_ord k l ord_k at ord_l
  simp only [k_neq_l, false_or] at ord_l
  simp_rw [exten_prop, enlarge_iff] at succ_eq; have succ_eq' := succ_eq
  specialize succ_eq l; specialize succ_eq' k
  simp only [set_in_itself_iff_false, k_neq_l, eq_comm, k_neq_l, or_false, or_true, iff_true, true_iff] at *
  apply false_if_isOrd_and_mutual_mem k l ord_k succ_eq' succ_eq

lemma exists_max_of_set_of_ord_aux (x y : S) (set_of_ord : ∀ k ∈ x ◁ y, IsOrd k)
    (x_has_max : ∃ l ∈ x, ∀ k ∈ x, (k ∈ l ∨ k = l)) :
    ∃ l ∈ x ◁ y, ∀ k ∈ x ◁ y, (k ∈ l ∨ k = l) := by
  rcases x_has_max with ⟨max_x, ⟨max_x_in_x, h_max_x⟩⟩
  have ord_max_x : IsOrd max_x := set_of_ord max_x (by simp_all only [enlarge_iff, true_or])
  have ord_y :  IsOrd y := set_of_ord y (by simp only [enlarge_iff, or_true])
  use if max_x ∈ y then y else max_x
  split_ifs with max_x_in_y
  · simp only [enlarge_iff, or_true, true_and]
    intros k hk
    refine hk.elim ?_ (fun a ↦ Or.inr a)
    intro k_in_x; specialize h_max_x k k_in_x
    left
    refine h_max_x.elim (isTrans_mem y max_x k ord_y.1 max_x_in_y) (by intro k_eq_max; subst k; exact max_x_in_y)
  · simp only [enlarge_iff, max_x_in_x, true_or, true_and]
    intros k hk
    refine hk.elim (h_max_x k) ?_
    intro k_eq_y; subst k
    have compar := compar_of_ord_ord y max_x ord_y ord_max_x
    simp_all only [enlarge_iff, true_or, or_true, or_false]

theorem exists_max_of_set_of_ord (x : S) (set_of_ord : ∀ k ∈ x, IsOrd k) (neq_emp : x ≠ ∅) :
    ∃ l ∈ x, ∀ k ∈ x, (k ∈ l ∨ k = l) := by sorry
  -- induction' x using HF.induction with x y hx _

  -- · simp_all
  -- · have x_set_of_ord : ∀ k ∈ x, ord k := by simp_rw [enlarge_iff] at set_of_ord; aesop
  --   specialize hx x_set_of_ord
  --   by_cases x_eq_emp : x = ∅
  --   · simp_rw [x_eq_emp, enlarge_iff, set_notin_empty, false_or]
  --     use y; simp_all
  --   · apply exists_max_of_enlarged_set_of_ord x y <;> simp_all

lemma exists_min_of_set_of_ord_aux (x y : S) (set_of_ord : ∀ k ∈ x ◁ y, IsOrd k)
    (x_has_min : ∃ l ∈ x, ∀ k ∈ x, (l ∈ k ∨ l = k)) :
    ∃ l ∈ x ◁ y, ∀ k ∈ x ◁ y, (l ∈ k ∨ l = k) := by
  rcases x_has_min with ⟨min_x, ⟨min_x_in_x, h_min_x⟩⟩
  have ord_min_x : IsOrd min_x := set_of_ord min_x (by simp_all only [enlarge_iff, true_or])
  have ord_y :  IsOrd y := set_of_ord y (by simp only [enlarge_iff, or_true])
  use if y ∈ min_x then y else min_x
  split_ifs with y_in_min_x
  · simp only [enlarge_iff, or_true, true_and] at *
    intros k hk
    refine hk.elim ?_ (fun a ↦ Or.inr (id (Eq.symm a)))
    intro k_in_x; specialize h_min_x k k_in_x
    left
    refine h_min_x.elim ?_ (by intro k_eq_min; subst k; exact y_in_min_x)
    intro min_x_in_k; apply isTrans_mem k min_x y (set_of_ord k hk).1 min_x_in_k y_in_min_x
  · simp only [enlarge_iff, min_x_in_x, true_or, true_and]
    intros k hk
    refine hk.elim (h_min_x k) ?_
    intro k_eq_y; subst k
    have compar := compar_of_ord_ord min_x y ord_min_x ord_y
    simp_all only [enlarge_iff, true_or, or_true, or_false]

theorem exists_min_of_set_of_ord (x : S) (set_of_ord : ∀ k ∈ x, IsOrd k) (neq_emp : x ≠ ∅) :
    ∃ l ∈ x, ∀ k ∈ x, (l ∈ k ∨ l = k) := by sorry
  -- induction' x using HF.induction with x y hx _
  -- · simp_all
  -- · have x_set_of_ord : ∀ k ∈ x, ord k := by simp_rw [enlarge_iff] at set_of_ord; aesop
  --   specialize hx x_set_of_ord
  --   by_cases x_eq_emp : x = ∅
  --   · simp_rw [x_eq_emp, enlarge_iff, set_notin_empty, false_or]
  --     use y; simp_all
  --   · apply exists_min_of_enlarged_set_of_ord x y <;> simp_all



end HF
