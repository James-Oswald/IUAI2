
-- This file covers chapter 2.1.2 of the book, about prefix codes.

import Mathlib
import IUAI2.c21.BinStr
import IUAI2.c21.Bijection


/--
We say that x is a prefix of y (denoted by x ⊑ y) if ∃z ∈ B∗ such
that xz = y.
-/
@[simp]
def BinStr.prefix (x y : 𝔹*) : Prop :=
  ∃ z, x ++ z = y

notation:50 x " ⊑ " y => BinStr.prefix x y

@[simp]
def BinStr.proper_prefix (x y : 𝔹*) : Prop :=
  ∃ z, x ++ z = y ∧ z ≠ []

notation:50 x " ⊏ " y => BinStr.proper_prefix x y

-- A set P ⊆ B∗ is prefix-free if no element of the set is a proper prefix of another.
@[simp]
def prefix_free (P : Set 𝔹*) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, ¬(x ⊏ y)

/--
A function c's range is prefix-free
-/
@[simp]
def prefix_free' (c : 𝔹* -> 𝔹*) : Prop :=
  prefix_free (Set.range c)

/--
A prefix code is an injective function from 𝔹* to 𝔹* whose range is prefix-free.
-/
class PrefixCode (c : 𝔹* → 𝔹*) : Prop where
  injective : Function.Injective c
  prefix_free : prefix_free' c

/--
The infinite family of prefix codes E_i : B∗→B∗, for i ∈ N, is defined as follows:
-/
@[simp]
def E : Nat -> 𝔹* -> 𝔹*
| 0, x => List.replicate (b0_to_nat x) true ++ [false]
| i + 1, x => E i (nat_to_b0 x.length) ++ x

@[simp]
def E_inv_aux : Nat -> Nat -> 𝔹* -> 𝔹*
| 0, s, x => x.take s
| n + 1, s, x => E_inv_aux n (b0_to_nat (x.take s)) (x.drop s)

@[simp]
def E_inv : Nat -> 𝔹* -> 𝔹*
| 0, x => nat_to_b0 (x.findIdx (· = false))
| n + 1, x => let p := (x.findIdx (· = false)); E_inv_aux n p (x.drop (p + 1))


-- @[simp]
-- def E_inv' : Nat -> 𝔹* -> 𝔹*
-- | 0, x => nat_to_b0 (x.findIdx (· = false) + 1)
-- | n + 1, x => let s := b0_to_nat (E_inv' n x); (x.drop s).take

-- -- Test the correctness of E_inv and E
-- #eval ∀ n : Fin 3 , ∀ m : Fin 100, E_inv n (E n (nat_to_b0 m)) = nat_to_b0 m

local notation:max "|" l "|" => List.length l

theorem E_inv_E_id (i : Nat) (x : 𝔹*) : E_inv i (E i x) = x := by
  -- induction i <;> induction x
  -- . case zero.nil => aesop
  -- . case zero.cons b x ih => simp_all; grind
  -- · case succ.nil n ih =>
  --   simp_all [E, E_inv]
  sorry





-- #eval (nat_to_b0 1000).toString
-- #eval (E 2 (nat_to_b0 1000)).toString

lemma E_zero_len (x : 𝔹*) : (E 0 x).length = b0_to_nat x + 1 := by
  simp_all only [E, b0_to_nat, List.length_append,
    List.length_replicate, List.length_cons, List.length_nil,
    zero_add]


-- @[simp]
-- def count_zeros (x : 𝔹*) : Nat :=
--   x.count false

-- lemma count_zeros_E_i (i : Nat) (x : 𝔹*) : count_zeros (E i x) = + count_zeros x := by
--   induction i <;> simp_all only [E, count_zeros, List.count_append,
--     List.count_replicate, List.count_cons, List.count_nil]

-- lemma count_zeros_not_equal {x y : 𝔹*} (h : count_zeros x ≠ count_zeros y) : x ≠ y := by
--   contrapose! h
--   rw [h]

-- The
@[simp]
def BinStr.first_zero (x : 𝔹*) : Nat :=
  x.findIdx (λ b => b = false)

lemma first_zero_replicate {z: 𝔹*} {n : Nat} :
BinStr.first_zero (List.replicate n true ++ false :: z) = n := by
  induction n <;> induction z <;> simp_all <;> grind

lemma first_zero_replicate' {z: 𝔹*} {n : Nat} :
BinStr.first_zero (List.replicate n true ++ [false] ++ z) = n := by
  induction n <;> induction z <;> simp_all <;> grind

lemma BinStr.eq_imp_len_eq {x y : 𝔹*} (h : x = y) : x.length = y.length := by
  rw [h]

-- If the first zero is at different positions, then the strings are different
lemma first_zero_neq {x y : 𝔹*} (h : x.first_zero ≠ y.first_zero) : x ≠ y := by
  contrapose! h
  rw [h]

-- If strings are equal, they on the first first zero, this is used in
-- The argument for Lemma 2.1.6
lemma first_zero_eq {x y : 𝔹*} (h : x = y) : x.first_zero = y.first_zero := by
  rw [h]


-- lemma neq_append {a b c d : 𝔹*} (H1 : c ≠ d) (h : a ++ c ≠ b ++ d) : a ≠ b := by


-- E_0 is injective
lemma E_0_injective : Function.Injective (E 0) := by
  simp only [Function.Injective, E, List.append_cancel_right_eq,
    List.replicate_inj, or_true, and_true]
  intros x y
  apply b0_to_nat_bijective.left

-- The range of E_0 is prefix-free
lemma E_0_prefix_free : prefix_free' (E 0) := by
  simp only [prefix_free', prefix_free, E, Set.range, Set.mem_setOf_eq, BinStr.proper_prefix,
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

lemma E_1_injective : Function.Injective (E 1) := by
  simp only [Function.Injective]
  unfold E
  intros x y H
  apply List.append_inj_right' H
  have H' := BinStr.eq_imp_len_eq H
  -- simp only [E, b0_to_nat, nat_to_b0, List.reverse_reverse, ne_eq, Nat.add_eq_zero_iff,
  --   List.length_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, nat_to_l1_to_nat,
  --   add_tsub_cancel_right, List.append_assoc, List.cons_append, List.nil_append, List.length_append,
  --   List.length_replicate, List.length_cons] at H'
  simp [List.length_append] at H'
  grind only

local notation:max "|" l "|" => List.length l

-- @[simp]
-- lemma List.take_append_length {A : Type} {l1 l2 : List A} : (l1 ++ l2).take l1.length = l1 := by
--   simp_all only [take_left']

-- @[simp]
-- lemma List.take_append_of_le_length' {n : Nat} {A : Type} {l1 l2 : List A} (h : n ≤ l1.length) :
-- (l1 ++ l2).take n = l1.take n := by
--   simp_all only [take_eq_left_iff, or_true]

-- lemma List.pref_eq_core {α : Type} {A B : List α}
-- (H1 : A = B.take A.length)
-- (H2 : B = A.take B.length) :
-- A = B := by
--   -- (no proof here)
--   grind


lemma E_i_injective (i : Nat) : Function.Injective (E i) := by
  induction i
  . case zero => exact E_0_injective
  . case succ i ih =>
    simp_all only [Function.Injective]
    unfold E
    intros x y H
    sorry
  -- induction i
  -- . case zero => exact E_0_injective
  -- . case succ i ih =>
  --   simp_all only [Function.Injective]
  --   unfold E
  --   intros x y H
  --   apply List.append_inj_right' H
  --   set A : 𝔹* := E i (nat_to_b0 x.length)
  --   set B : 𝔹* := E i (nat_to_b0 y.length)

  --   have : (A ++ x).take A.length = (B ++ y).take A.length := by grind only
  --   have : (A ++ x).take A.length = A := by exact List.take_append_length
  --   have : A = (B ++ y).take A.length := by grind

  --   have : (B ++ y).take B.length = (A ++ x).take B.length := by grind only
  --   have : (B ++ y).take B.length = B := by exact List.take_append_length
  --   have : B = (A ++ x).take B.length := by grind

  --   by_cases C1: A.length ≤ B.length
  --   . case pos =>
  --     have : A = B.take A.length := by grind [List.take_append_of_le_length']
  --     have : B = A.take B.length := by aesop





  --   . case neg => sorry
      -- have : E i (nat_to_b0 |x|) = E i (nat_to_b0 |y|) := by
      --   grind
      -- apply ih
      -- apply nat_to_b0_bijective.left
      -- exact this



    -- -- apply nat_to_b0_bijective.left
    -- -- apply ih
    -- -- apply List.append_inj_left H

    -- have H' := BinStr.eq_imp_len_eq H
    -- simp only [List.length_append] at H'




    -- by_cases! C1: x = y
    -- . case pos => grind
    -- . case neg =>
    --   apply List.append_inj_right' H
    --   by_cases H2: |x| = |y|
    --   . case pos => aesop
    --   . case neg =>
    --     apply nat_to_b0_bijective.left
    --     by_cases H3 : nat_to_b0 |x| = nat_to_b0 |y|
    --     . case pos => exact H3
    --     . case neg =>
    --       apply ih
    --       by_cases H4 : E i (nat_to_b0 |x|) = E i (nat_to_b0 |y|)
    --       . case pos => exact H4
    --       . case neg =>
    --         apply List.append_inj_left H
    --         have H' := BinStr.eq_imp_len_eq H
    --         simp only [List.length_append] at H'
    --         by_contra
    --         simp_all
    --         aesop


    -- apply List.append_inj_right' H
    -- have H' := BinStr.eq_imp_len_eq H
    -- simp only [List.length_append] at H'
    -- have H'' := @ih (nat_to_b0 x.length) (nat_to_b0 y.length)
    -- apply nat_to_b0_bijective.left
    -- apply H''
    -- clear H''
    -- apply List.append_inj_left H
    -- by_cases H2 : (E i (nat_to_b0 x.length)).length = (E i (nat_to_b0 y.length)).length
    -- . case pos => aesop
    -- . case neg =>





    -- --by_contra! C
    -- apply List.append_inj_right' H
    -- apply nat_to_b0_bijective.left
    -- apply ih
    -- by_cases H2 : x = y
    -- . case pos => aesop
    -- . case neg =>


    -- have H' := BinStr.eq_imp_len_eq H
    -- simp only [List.length_append] at H'
    -- apply List.append_inj_right' H




    -- -- have H'' := @ih (nat_to_b0 x.length) (nat_to_b0 y.length)
    -- -- apply nat_to_b0_bijective.left
    -- -- apply H''


    -- apply List.append_inj_right' H
    -- apply nat_to_b0_bijective.left
    -- apply ih
    -- apply List.append_inj_left' H




        -- H is now impossible the function will have different lengths
    -- have H'' : (E i (nat_to_b0 x.length)).length + x.length = (E i (nat_to_b0 y.length)).length + y.length := by
    --   exact H'
    -- have H''' : (E i (nat_to_b0 x.length)).length = (E i (nat_to_b0 y.length)).length + y.length - x.length := by
    --   grind



    -- by_cases H2 : x = y
    -- · case pos => grind only
    -- . case neg =>

  -- simp only [Function.Injective]
  -- unfold E
  -- intros x y H
  -- apply List.append_inj_right' H
  -- have H' := BinStr.eq_imp_len_eq H
  -- -- simp only [E, b0_to_nat, nat_to_b0, List.reverse_reverse, ne_eq, Nat.add_eq_zero_iff,
  -- --   List.length_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, nat_to_l1_to_nat,
  -- --   add_tsub_cancel_right, List.append_assoc, List.cons_append, List.nil_append, List.length_append,
  -- --   List.length_replicate, List.length_cons] at H'
  -- simp [List.length_append] at H'
  -- grind only

  -- apply nat_to_b0_bijective.left
  -- apply E_0_injective
  -- have H := E_0_injective
  -- simp only [Function.Injective] at H
  -- have H' := @H (nat_to_b0 x.length) (nat_to_b0 y.length)


example (i : Nat) (x y z : 𝔹*) (H : (E i x) ++ z = E i y) :
x.length = y.length := by
  induction i
  . case zero =>
    unfold E at H
    have H' := first_zero_eq H
    simp only [first_zero_replicate, first_zero_replicate'] at H'
    congr
    exact b0_to_nat_bijective.left H'
  . case succ i ih =>
    unfold E at H
    sorry


lemma E_1_prefix_free : prefix_free' (E 1) := by
  simp [-E]
  intro x y z H
  -- unfold E at H
  -- have H' := BinStr.eq_imp_len_eq H
  -- simp only [List.length_append] at H'
  by_cases H2 : x = y
  . case pos => subst H2; simp_all only [List.append_right_eq_self]
  . case neg =>
    sorry

    --unfold E at H








-- Lemma 2.1.6 (i-th order code is prefix code)
-- theorem ith_order_E_is_prefix_code (i : Nat) : PrefixCode (E i) := by
--   induction i
--   · case zero =>
--     constructor
--     · case injective =>
--       simp only [Function.Injective, E, List.append_cancel_right_eq,
--         List.replicate_inj, or_true, and_true]
--       intros x y
--       apply b0_to_nat_bijective.left
--     · case prefix_free =>
--       simp only [prefix_free, E, Set.mem_setOf_eq, 𝔹*.proper_prefix,
--         ne_eq, not_exists, not_and, Decidable.not_not, forall_exists_index, forall_apply_eq_imp_iff,
--         List.append_assoc, List.cons_append, List.nil_append]
--       intros x y z H
--       by_cases H2 : x = y
--       · case pos =>
--         subst H2
--         simp_all only [b0_to_nat, List.append_cancel_left_eq, List.cons.injEq, true_and]
--       · case neg =>
--         have : b0_to_nat x ≠ b0_to_nat y := by
--           contrapose! H2
--           apply b0_to_nat_bijective.left
--           exact H2
--         contrapose! H
--         apply first_zero_neq
--         rw [first_zero_replicate, first_zero_replicate]
--         exact this
--   . case succ i ih =>
--     have ⟨inj, pf⟩ := ih
--     constructor
--     · case injective =>
--       simp_all only [Function.Injective, E]
--       intros x y H
--       --have inj' := (@inj (nat_to_b0 x.length) (nat_to_b0 y.length))
--       sorry
--     . case prefix_free =>
--       simp_all only [prefix_free, E, Set.mem_setOf_eq, 𝔹*.proper_prefix,
--         ne_eq, not_exists, not_and, Decidable.not_not, forall_exists_index, forall_apply_eq_imp_iff,
--         List.append_assoc]
--       intro x y z H
--       by_cases H2 : x = y
--       · case pos =>
--         subst H2
--         simp_all only [nat_to_b0, List.append_cancel_left_eq, List.append_right_eq_self]
--       · case neg =>
--         sorry













--   · case succ i ih => sorry
