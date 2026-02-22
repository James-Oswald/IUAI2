
import Mathlib

-- Utility Lemmas
lemma iUnion_split {α} (s : ℕ → Set α) :
  (⋃ n, s n) = s 0 ∪ (⋃ n, s (n + 1)) := by
  symm
  apply sup_iSup_nat_succ s

lemma iUnion_split_2 {α} (s : ℕ → Set α) :
  (⋃ n, s n) = s 0 ∪ s 1 ∪ (⋃ n, s (n + 2)) := by
  rw [iUnion_split, iUnion_split]
  grind only [= Set.mem_union, cases Or]

lemma tsum_split {f : ℕ -> Real} {H : Summable f}:
  (∑' i, f i) = f 0 + (∑' n, f (n + 1)) := by
  apply Summable.tsum_eq_zero_add
  exact H

lemma tsum_split_2 {f : ℕ -> Real} {H : Summable f} :
  (∑' i, f i) = f 0 + f 1 + (∑' i, f (i + 2)) := by
  have H := (Summable.sum_add_tsum_nat_add 2 H)
  have H' : Finset.range 2 = {0, 1} := by rfl
  rw [H', Finset.sum_pair] at H
  symm
  exact H
  simp only [ne_eq, zero_ne_one, not_false_eq_true]
