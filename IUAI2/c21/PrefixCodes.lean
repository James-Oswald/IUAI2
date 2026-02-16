
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

notation:50 x:51 " ⊑ " y:51 => BinStr.prefix x y
notation:50 x:51 " ¬⊑ " y:51 => ¬ x ⊑ y

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
notation:80 l:81 " ^ " n:80 => List.flatten (List.replicate n l)

@[simp]
lemma list_pow_eq_replicate {α : Type*} (n : ℕ) (a : α)
    : [a] ^ n = List.replicate n a := by
  induction n <;> grind

@[simp]
def E : Nat -> 𝔹* -> 𝔹*
| 0, x => [true] ^ (b0_to_nat x) ++ [false]
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

-- local notation:max "|" l "|" => List.length l

-- theorem E_inv_E_id (i : Nat) (x : 𝔹*) : E_inv i (E i x) = x := by
--   -- induction i <;> induction x
--   -- . case zero.nil => aesop
--   -- . case zero.cons b x ih => simp_all; grind
--   -- · case succ.nil n ih =>
--   --   simp_all [E, E_inv]
--   sorry





-- #eval (nat_to_b0 1000).toString
-- #eval (E 2 (nat_to_b0 1000)).toString

lemma E_zero_len (x : 𝔹*) : (E 0 x).length = b0_to_nat x + 1 := by
  simp_all only [E, b0_to_nat, List.length_append,
    list_pow_eq_replicate, List.length_replicate, List.length_cons, List.length_nil,
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
    list_pow_eq_replicate, List.replicate_inj, or_true, and_true]
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
    rw [list_pow_eq_replicate, first_zero_replicate, list_pow_eq_replicate, first_zero_replicate]
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

lemma PrefixCode_pairwise (code : 𝔹* → 𝔹*) :
    PrefixCode code ↔ ∀ x y : 𝔹*, x ≠ y → code x ¬⊑ code y := by
  constructor
  · intro ⟨inj, pf⟩
    intros x y hne
    intro ⟨z, hz⟩
    by_cases h : z = []
    · subst h
      simp only [List.append_nil] at hz
      have : x = y := inj hz
      exact hne this
    · simp only [prefix_free', prefix_free, Set.mem_range, BinStr.proper_prefix, ne_eq,
        not_exists, not_and, Decidable.not_not, forall_exists_index, forall_apply_eq_imp_iff] at pf
      grind only
  · intro h
    constructor
    · intros x y heq
      by_contra hne
      have h1 : code x ¬⊑ code y := h x y hne
      have h2 : code x ⊑ code y := ⟨[], by grind only⟩
      exact h1 h2
    · simp only [prefix_free', prefix_free, Set.mem_range, BinStr.proper_prefix,
        forall_exists_index]
      intros cx x hx cy y hy hex
      obtain ⟨z, hz1, hz2⟩ := hex
      by_cases hxy : x = y
      · subst hxy
        rw [← hx, ← hy] at hz1
        simp only [List.append_right_eq_self] at hz1
        exact hz2 hz1
      · have h1 : code x ¬⊑ code y := h x y hxy
        rw [hx, hy] at h1
        have h2 : cx ⊑ cy := ⟨z, hz1⟩
        exact h1 h2

lemma append_pow_pow_where_same_base {α : Type*} (l1 : List α) (m n : ℕ) :
    l1 ^ (m + n) = l1 ^ m ++ l1 ^ n := by
  induction m with
  | zero => grind only [= List.replicate_zero, =_ List.flatten_append]
  | succ => grind only [= List.replicate_succ, = List.flatten_cons, usr List.append_assoc]

lemma pow_split_less {α : Type*} (l : List α) (m n : Nat) (h : m < n) :
    l ^ n = l ^ m ++ l ^ (n - m) := by
  have : n = m + (n - m) := by grind only
  grind only [append_pow_pow_where_same_base]

lemma Prefix_with_shared_prefix (x y z : 𝔹*) : z ++ x ⊑ z ++ y ↔ x ⊑ y := by
  induction z <;>  simp_all only [BinStr.prefix, List.append_assoc, List.append_cancel_left_eq,
    List.cons_append, List.cons.injEq, true_and]

lemma Prefix_implies_length_le (x y : 𝔹*) :
    x ⊑ y → |x| ≤ |y| := by
  induction x with
  | nil => grind only [List.length_nil]
  | cons => grind only [BinStr.prefix, List.length_append]

lemma nat_to_b0_is_injective (m n : ℕ) :
    nat_to_b0 m = nat_to_b0 n → m = n := by
  grind only [nat_to_b0_to_nat]

lemma b0_to_nat_is_injective (x y : 𝔹*) :
    b0_to_nat x = b0_to_nat y → x = y := by
  grind only [b0_to_nat_to_b0]

lemma length_pow {α : Type*} (l : List α) (n : ℕ) :
    |l^n| = n * |l| := by
  induction n with
  | zero =>
    grind only [List.length_flatten, List.replicate_zero, List.map_nil, List.sum_nil]
  | succ =>
    grind only [= List.length_flatten, = List.replicate_succ, = List.map_cons, = List.sum_cons]

lemma false_not_prefix_true_pow_false (n : Nat) (h : n > 0) :
    [false] ¬⊑ [true] ^ n ++ [false] := by
  intro ⟨z, hz⟩
  cases n <;> grind only [
    = List.replicate_succ, = List.cons_append, = List.flatten_cons, usr List.append_assoc]

lemma greater_length_not_prefix (x y : 𝔹*) (h : |x| > |y|) : x ¬⊑ y := by
  intro h
  have : |x| ≤ |y| := Prefix_implies_length_le x y h
  grind only

lemma PrefixCode_E_0 : PrefixCode (E 0) := by
  rw [PrefixCode_pairwise]
  intro x y hne
  have : x ≠ y := hne
  show E 0 x ¬⊑ E 0 y

  have s1 : E 0 x = [true] ^ (b0_to_nat x) ++ [false] := E.eq_def 0 x
  have s2 : E 0 y = [true] ^ (b0_to_nat y) ++ [false] := E.eq_def 0 y
  have : b0_to_nat x ≠ b0_to_nat y := by grind only [= b0_to_nat.eq_1, b0_to_nat_is_injective]
  have : b0_to_nat x < b0_to_nat y ∨ b0_to_nat x > b0_to_nat y := by grind only
  cases this
  · next h2 =>
    have : E 0 y = [true] ^ b0_to_nat x ++ [true] ^ (b0_to_nat y - b0_to_nat x) ++ [false] := by
      grind only [pow_split_less]
    have : [false] ¬⊑ [true] ^ (b0_to_nat y - b0_to_nat x) ++ [false] := by
      grind only [false_not_prefix_true_pow_false]
    have : [true] ^ b0_to_nat x ++ [false] ¬⊑
        [true] ^ b0_to_nat x ++ [true] ^ (b0_to_nat y - b0_to_nat x) ++ [false] := by
      grind only [usr List.append_assoc, Prefix_with_shared_prefix]
    have : [true] ^ b0_to_nat x ++ [false] ¬⊑ [true] ^ b0_to_nat y ++ [false] := by
      grind only
    have : E 0 x ¬⊑ E 0 y := by
      grind only
    exact this
  · next h2 =>
    have : |E 0 x| > |E 0 y| := by
      grind only [E_zero_len]
    have : E 0 x ¬⊑ E 0 y := by
      grind only [greater_length_not_prefix]
    exact this


lemma prefix_and_length_eq_implies_eq (x y : 𝔹*) (h1 : x ⊑ y) (h2 : |x| = |y|) : x = y := by
  simp_all only [BinStr.prefix]
  obtain ⟨w, h⟩ := h1
  subst h
  simp_all only [List.length_append, Nat.left_eq_add, List.length_eq_zero_iff, List.append_nil]

lemma prefix_incomparable_append (A B x y : 𝔹*)
    (h1 : A ¬⊑ B) (h2 : B ¬⊑ A) : A ++ x ¬⊑ B ++ y := by
  intro ⟨z, hz⟩
  have trichotomy : |A| < |B| ∨ |A| = |B| ∨ |A| > |B| := by grind only
  cases trichotomy
  · next hlt =>
      have : A ⊑ B := by
        have : (A ++ x ++ z).take |A| = (B ++ y).take |A| := by grind only
        have : A = (B ++ y).take |A| := by grind only [usr List.append_assoc, List.take_left']
        have : A = B.take |A| := by grind only [List.take_append_of_le_length]
        use B.drop |A|
        grind only [List.take_append_drop]
      grind only
  · next rest =>
      cases rest
      · next heq =>
          have : (A ++ x ++ z).take |A| = (B ++ y).take |B| := by grind only
          have : A = B := by grind only [usr List.append_assoc, List.take_left']
          have : A ⊑ B := by use []; grind only
          grind only
      · next hgt =>
          have : B ⊑ A := by
            have : (B ++ y).take |B| = (A ++ x ++ z).take |B| := by grind only
            have : B = (A ++ x ++ z).take |B| := by grind only [List.take_left']
            have : B = A.take |B| := by
              grind only [usr List.append_assoc, List.take_append_of_le_length]
            use A.drop |B|
            grind only [!List.take_append_drop]
          grind only

lemma PrefixCode_E_succ (i : Nat) (ih : PrefixCode (E i)) : PrefixCode (E (i + 1)) := by
  rw [PrefixCode_pairwise]
  intro x y hne
  have : x ≠ y := hne
  show E (i + 1) x ¬⊑ E (i + 1) y

  have s1 : E (i + 1) x = E i (nat_to_b0 |x|) ++ x := E.eq_def (i + 1) x
  have s2 : E (i + 1) y = E i (nat_to_b0 |y|) ++ y := E.eq_def (i + 1) y

  by_cases h_len : |x| = |y|
  · next =>
      have : nat_to_b0 |x| = nat_to_b0 |y| := by grind only
      have : E i (nat_to_b0 |x|) = E i (nat_to_b0 |y|) := by grind only
      have : x ¬⊑ y := by grind only [prefix_and_length_eq_implies_eq]
      have : E i (nat_to_b0 |x|) ++ x ¬⊑ E i (nat_to_b0 |y|) ++ y := by
        grind only [Prefix_with_shared_prefix]
      have : E (i + 1) x ¬⊑ E (i + 1) y := by grind only
      exact this

  · next =>
      have : nat_to_b0 |x| ≠ nat_to_b0 |y| := by grind only [nat_to_b0_is_injective]
      have ih_pair := PrefixCode_pairwise (E i)
      have : ∀ a b, a ≠ b → E i a ¬⊑ E i b := by grind only
      have : E i (nat_to_b0 |y|) ¬⊑ E i (nat_to_b0 |x|) := by grind only
      have : E i (nat_to_b0 |x|) ++ x ¬⊑ E i (nat_to_b0 |y|) ++ y := by
        grind only [prefix_incomparable_append]
      have : E (i + 1) x ¬⊑ E (i + 1) y := by grind only
      exact this

theorem PrefixCode_E_i (i : Nat) : PrefixCode (E i) := by
   -- Lemma 2.1.6 from the book
  induction i with
  | zero => exact PrefixCode_E_0
  | succ i' ih => exact PrefixCode_E_succ i' ih


lemma prefix_refl (x : 𝔹*) : x ⊑ x := by
  use []
  grind only

theorem prepend_prefix_code_injective {c : 𝔹* → 𝔹*} (h : PrefixCode c) (x1 y1 x2 y2 : 𝔹*) : c x1 ++ y1 = c x2 ++ y2 → x1 = x2 ∧ y1 = y2 := by
  -- Theorem 2.1.7 from the book
  have hp : ∀ (x y : 𝔹*), x ≠ y → ¬c x ⊑ c y := by rw [PrefixCode_pairwise] at h; exact h
  show c x1 ++ y1 = c x2 ++ y2 → x1 = x2 ∧ y1 = y2
  suffices x1 ≠ x2 ∨ y1 ≠ y2 → c x1 ++ y1 ≠ c x2 ++ y2 by grind only
  intro h1
  have : x1 ≠ x2 ∨ y1 ≠ y2 := h1
  have : x1 ≠ x2 ∨ (x1 = x2 ∧ y1 ≠ y2) := by grind only
  cases this
  · next h2 =>
    have : x1 ≠ x2 := h2
    have : c x1 ≠ c x2 := by grind [h.injective]
    have s1 : c x1 ¬⊑ c x2 := by grind only
    have s1 : c x2 ¬⊑ c x1 := by grind only
    have : c x1 ++ y1 ¬⊑ c x2 ++ y2 := by grind [prefix_incomparable_append]
    have : c x1 ++ y1 ≠ c x2 ++ y2 := by grind [prefix_refl]
    exact this
  · next h2 =>
    have s1 : x1 = x2 ∧ y1 ≠ y2 := h2
    have : c x1 = c x2 := by grind only
    have : c x1 ++ y1 ≠ c x2 ++ y2 := by grind only [List.append_cancel_left_eq]
    exact this

-- lemma E_i_injective (i : Nat) : Function.Injective (E i) := by
--   induction i
--   . case zero => exact E_0_injective
--   . case succ i ih =>
--     simp_all only [Function.Injective]
--     unfold E
--     intros x y H
--     sorry
--   -- induction i
--   -- . case zero => exact E_0_injective
--   -- . case succ i ih =>
--   --   simp_all only [Function.Injective]
--   --   unfold E
--   --   intros x y H
--   --   apply List.append_inj_right' H
--   --   set A : 𝔹* := E i (nat_to_b0 x.length)
--   --   set B : 𝔹* := E i (nat_to_b0 y.length)

--   --   have : (A ++ x).take A.length = (B ++ y).take A.length := by grind only
--   --   have : (A ++ x).take A.length = A := by exact List.take_append_length
--   --   have : A = (B ++ y).take A.length := by grind

--   --   have : (B ++ y).take B.length = (A ++ x).take B.length := by grind only
--   --   have : (B ++ y).take B.length = B := by exact List.take_append_length
--   --   have : B = (A ++ x).take B.length := by grind

--   --   by_cases C1: A.length ≤ B.length
--   --   . case pos =>
--   --     have : A = B.take A.length := by grind [List.take_append_of_le_length']
--   --     have : B = A.take B.length := by aesop





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


-- example (i : Nat) (x y z : 𝔹*) (H : (E i x) ++ z = E i y) :
-- x.length = y.length := by
--   induction i
--   . case zero =>
--     unfold E at H
--     have H' := first_zero_eq H
--     simp only [first_zero_replicate, first_zero_replicate'] at H'
--     congr
--     exact b0_to_nat_bijective.left H'
--   . case succ i ih =>
--     unfold E at H
--     sorry


-- lemma E_1_prefix_free : prefix_free' (E 1) := by
--   simp [-E]
--   intro x y z H
--   -- unfold E at H
--   -- have H' := BinStr.eq_imp_len_eq H
--   -- simp only [List.length_append] at H'
--   by_cases H2 : x = y
--   . case pos => subst H2; simp_all only [List.append_right_eq_self]
--   . case neg =>
--     sorry

--     unfold E at H








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
