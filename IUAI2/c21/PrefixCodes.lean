
-- This file covers chapter 2.1.2 of the book, about prefix codes.

import IUAI2.c21.BinStr
import IUAI2.c21.Bijection
import Mathlib

/--
We say that x is a prefix of y (denoted by x ⊑ y) if ∃z ∈ B∗ such
that xz = y.
-/
@[simp]
def BinStr.prefix (x y : BinStr) : Prop :=
  ∃ z, x ++ z = y

notation:50 x " ⊑ " y => BinStr.prefix x y

@[simp]
def BinStr.proper_prefix (x y : BinStr) : Prop :=
  ∃ z, x ++ z = y ∧ z ≠ []

notation:50 x " ⊏ " y => BinStr.proper_prefix x y

@[simp]
def prefix_free (P : Set BinStr) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, ¬(x ⊏ y)

/--
A set P ⊆ B∗ is called prefix-free if no element of the set is a proper prefix of another.
Given an injection c:B∗→B∗, if {c(x):x∈B∗} is prefix-free, then we call c a prefix-code.
-/
class PrefixCode (c : BinStr → BinStr) : Prop where
  injective : Function.Injective c
  prefix_free : prefix_free { c x | x : BinStr }

/--
The infinite family of prefix codes E_i : B∗→B∗, for i ∈ N, is defined as follows:
-/
@[simp]
def E : Nat -> BinStr -> BinStr
| 0, x => List.replicate (b0_to_nat x) true ++ [false]
| i + 1, x => E i (nat_to_b0 x.length) ++ x
-- λ x =>
--   if i = 0 then
--     List.replicate (b0_to_nat x) true ++ [false]
--   else
--     E (i - 1) (nat_to_b0 x.length) ++ x

lemma E_zero_len (x : BinStr) : (E 0 x).length = b0_to_nat x + 1 := by
  simp_all only [E, b0_to_nat, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil,
    zero_add]

@[simp]
def count_zeros (x : BinStr) : Nat :=
  x.count false

lemma count_zeros_not_equal {x y : BinStr} (h : count_zeros x ≠ count_zeros y) : x ≠ y := by
  contrapose! h
  rw [h]

@[simp]
def first_zero (x : BinStr) : Nat :=
  x.findIdx (λ b => b = false)

lemma first_zero_replicate {z: BinStr} {n : Nat} : first_zero (List.replicate n true ++ false :: z) = n := by
  induction n <;> induction z <;> simp_all <;> grind


-- If the first zero is at different positions, then the strings are different
lemma first_zero_neq {x y : BinStr} (h : first_zero x ≠ first_zero y) : x ≠ y := by
  contrapose! h
  rw [h]

-- If strings are equal, they agree up to the first zero
lemma first_zero_eq {x y : BinStr} (h : x = y) : first_zero x = first_zero y := by
  rw [h]

-- -- Two binary strings are different if they have different lengths.
-- lemma BinStr.neq_iff_length_neq {x  y : BinStr} (h : x.length ≠ y.length) : x ≠ y := by
--   contrapose! h
--   rw [h]

-- example {α : Type} {a : α} (m n : Nat) (H : n ≠ m) :
-- List.replicate n a ≠ List.replicate m a := by

-- All bits following a zero must be the same for two strings to be equal
-- lemma name_pending {x y : BinStr} ()

theorem ith_order_E_is_prefix_code (i : Nat) : PrefixCode (E i) := by
  induction i
  · case zero =>
    constructor
    · case injective =>
      simp only [Function.Injective, E, List.append_cancel_right_eq,
        List.replicate_inj, or_true, and_true]
      intros x y
      apply b0_to_nat_bijective.left
    · case prefix_free =>
      simp only [prefix_free, E, Set.mem_setOf_eq, BinStr.proper_prefix,
        ne_eq, not_exists, not_and, Decidable.not_not, forall_exists_index, forall_apply_eq_imp_iff,
        List.append_assoc, List.cons_append, List.nil_append]
      intros x y z H
      by_cases H2 : x = y
      · case pos =>
        subst H2
        simp_all only [b0_to_nat, List.append_cancel_left_eq, List.cons.injEq, true_and]
      · case neg =>
        have : b0_to_nat x ≠ b0_to_nat y := by
          contrapose! H2
          apply b0_to_nat_bijective.left
          exact H2
        contrapose! H
        apply first_zero_neq
        rw [first_zero_replicate, first_zero_replicate]
        exact this
  . case succ i ih =>
    have ⟨inj, pf⟩ := ih
    constructor
    · case injective =>
      simp_all only [Function.Injective, E]
      intros x y H
      --have inj' := (@inj (nat_to_b0 x.length) (nat_to_b0 y.length))
      sorry
    . case prefix_free =>
      simp_all only [prefix_free, E, Set.mem_setOf_eq, BinStr.proper_prefix,
        ne_eq, not_exists, not_and, Decidable.not_not, forall_exists_index, forall_apply_eq_imp_iff,
        List.append_assoc]
      intro x y z H
      by_cases H2 : x = y
      · case pos =>
        subst H2
        simp_all only [nat_to_b0, List.append_cancel_left_eq, List.append_right_eq_self]
      · case neg =>
        sorry













  · case succ i ih => sorry
