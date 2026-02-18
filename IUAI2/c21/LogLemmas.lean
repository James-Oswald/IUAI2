
import Mathlib

@[grind =, simp]
lemma log2_zero : (0).log2 = 0 := by
  rfl

@[grind =, simp]
lemma log2_one : (1).log2 = 0 := by
  rfl

@[grind ., grind →]
lemma log2_mono {n m : ℕ} : n ≤ m → n.log2 ≤ m.log2 := by
  repeat rw [Nat.log2_eq_log_two]
  have := @Nat.log_mono_right 2 n m
  grind only

@[grind =, simp]
lemma log2_two_mul (n : ℕ) (h : n ≠ 0) : (2 * n).log2 = n.log2 + 1 := Nat.log2_two_mul h

@[grind ., grind! ., grind! →]
lemma log2_of_plus_le_log2 {n m : ℕ} : m ≤ n → (n + m).log2 ≤ n.log2 + 1 := by
  intro h
  have : m ≤ n := h

  match mh: n with
  | 0 =>
    grind only
  | n' + 1 =>
    have : (n + m).log2 ≤ (2 * n).log2 := log2_mono (by grind)
    grind only [log2_two_mul]
