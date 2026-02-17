
-- This file covers chapter 2.1.2 of the book, about prefix codes.

import Mathlib
import IUAI2.c21.BinStr
import IUAI2.c21.Bijection


-------------------------------------------------------------------------------
-- List Powers
-------------------------------------------------------------------------------

notation:80 l:81 " ^ " n:80 => List.flatten (List.replicate n l)

@[simp]
lemma list_pow_eq_replicate {α : Type*} (n : ℕ) (a : α)
: [a] ^ n = List.replicate n a := by
  induction n <;> grind

lemma list_pow_add {α : Type*} (l1 : List α) (m n : ℕ) :
l1 ^ (m + n) = l1 ^ m ++ l1 ^ n := by
  induction m with
  | zero => grind only [= List.replicate_zero, =_ List.flatten_append]
  | succ => grind only [= List.replicate_succ, = List.flatten_cons, usr List.append_assoc]

lemma pow_split_less {α : Type*} (l : List α) (m n : Nat) (h : m < n) :
l ^ n = l ^ m ++ l ^ (n - m) := by
  have : n = m + (n - m) := by grind only
  grind only [list_pow_add]

lemma length_pow {α : Type*} (l : List α) (n : ℕ) :
ℓ (l^n) = n * ℓ l := by
  induction n with
  | zero =>
    grind only [List.length_flatten, List.replicate_zero, List.map_nil, List.sum_nil]
  | succ =>
    grind only [= List.length_flatten, = List.replicate_succ, = List.map_cons, = List.sum_cons]


-------------------------------------------------------------------------------
-- First Zeros
-------------------------------------------------------------------------------

@[simp]
def BinStr.first_zero (x : 𝔹*) : Nat :=
  x.findIdx (λ b => b = false)

lemma first_zero_replicate {z: 𝔹*} {n : Nat} :
BinStr.first_zero (List.replicate n true ++ false :: z) = n := by
  induction n <;> induction z <;> simp_all <;> grind

lemma first_zero_replicate' {z: 𝔹*} {n : Nat} :
BinStr.first_zero (List.replicate n true ++ [false] ++ z) = n := by
  induction n <;> induction z <;> simp_all <;> grind

-- lemma BinStr.eq_imp_len_eq {x y : 𝔹*} (h : x = y) : ℓ x = ℓ y := by
--   rw [h]

-- If the first zero is at different positions, then the strings are different
lemma first_zero_neq {x y : 𝔹*} (h : x.first_zero ≠ y.first_zero) : x ≠ y := by
  contrapose! h
  rw [h]


-------------------------------------------------------------------------------
-- String Prefixes
-------------------------------------------------------------------------------

/--
We say that x is a prefix of y (denoted by x ⊑ y) if ∃z ∈ B∗ such
that xz = y.
-/
@[simp]
def BinStr.prefix (x y : 𝔹*) : Prop :=
  ∃ z, x ++ z = y

notation:50 x:51 " ⊑ " y:51 => BinStr.prefix x y
notation:50 x:51 " ⋢ " y:51 => ¬ x ⊑ y

@[simp]
def BinStr.proper_prefix (x y : 𝔹*) : Prop :=
  ∃ z, x ++ z = y ∧ z ≠ []

notation:50 x " ⊏ " y => BinStr.proper_prefix x y

lemma prefix_refl (x : 𝔹*) : x ⊑ x := by
  use []
  grind only

lemma prefix_with_shared_prefix (x y z : 𝔹*) :
z ++ x ⊑ z ++ y ↔ x ⊑ y := by
  induction z <;>
  simp_all only [BinStr.prefix, List.append_assoc, List.append_cancel_left_eq,
    List.cons_append, List.cons.injEq, true_and]

lemma prefix_implies_length_le (x y : 𝔹*) :
x ⊑ y → ℓ x ≤ ℓ y := by
  induction x with
  | nil => grind only [List.length_nil]
  | cons => grind only [BinStr.prefix, List.length_append]

lemma false_not_prefix_true_pow_false (n : Nat) (h : n > 0) :
[false] ⋢ [true] ^ n ++ [false] := by
  intro ⟨z, hz⟩
  cases n <;> grind only [
    = List.replicate_succ, = List.cons_append, = List.flatten_cons, usr List.append_assoc]

lemma greater_length_not_prefix (x y : 𝔹*) (h : ℓ x > ℓ y) : x ⋢ y := by
  intro h
  have : ℓ x ≤ ℓ y := prefix_implies_length_le x y h
  grind only

-- If x is a prefix of y and they have the same length, then they are equal
lemma prefix_and_length_eq_implies_eq
(x y : 𝔹*) (h1 : x ⊑ y) (h2 : ℓ x = ℓ y) : x = y := by
  simp_all only [BinStr.prefix]
  obtain ⟨w, h⟩ := h1
  subst h
  simp_all only [List.length_append, Nat.left_eq_add,
    List.length_eq_zero_iff, List.append_nil]

lemma prefix_incomparable_append (A B x y : 𝔹*)
(h1 : A ⋢ B) (h2 : B ⋢ A) : A ++ x ⋢ B ++ y := by
  intro ⟨z, hz⟩
  rcases lt_trichotomy (ℓ A) (ℓ B) with (hlt | heq | hgt)
  · case inl =>
    have : A ⊑ B := by
      have : (A ++ x ++ z).take ℓ A = (B ++ y).take ℓ A := by grind only
      have : A = (B ++ y).take ℓ A := by grind only [usr List.append_assoc, List.take_left']
      have : A = B.take ℓ A := by grind only [List.take_append_of_le_length]
      use B.drop ℓ A
      grind only [List.take_append_drop]
    grind only
  · case inr.inl =>
    have : (A ++ x ++ z).take ℓ A = (B ++ y).take ℓ B := by grind only
    have : A = B := by grind only [usr List.append_assoc, List.take_left']
    have : A ⊑ B := by use []; grind only
    grind only
  · case inr.inr =>
    have : B ⊑ A := by
      have : (B ++ y).take ℓ B = (A ++ x ++ z).take ℓ B := by grind only
      have : B = (A ++ x ++ z).take ℓ B := by grind only [List.take_left']
      have : B = A.take ℓ B := by
        grind only [usr List.append_assoc, List.take_append_of_le_length]
      use A.drop ℓ B
      grind only [!List.take_append_drop]
    grind only

-------------------------------------------------------------------------------
-- Prefix Freeness
-------------------------------------------------------------------------------

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

-------------------------------------------------------------------------------
-- Prefix Codes
-------------------------------------------------------------------------------

/--
A prefix code is an injective function from 𝔹* to 𝔹* whose range is prefix-free.
-/
class PrefixCode (c : 𝔹* → 𝔹*) : Prop where
  injective : Function.Injective c
  prefix_free : prefix_free' c

/--
Kyle's Equivalent Characterization of Prefix Codes:
c is a prefix code (injective and prefix-free) iff for all distinct x and y,
c x is not a prefix of c y.
-/
theorem PrefixCode_pairwise (c : 𝔹* → 𝔹*) :
PrefixCode c ↔ ∀ x y : 𝔹*, x ≠ y → c x ⋢ c y := by
  constructor
  · case mp =>
    rintro ⟨inj, pf⟩ x y hne ⟨z, hz⟩
    by_cases h : z = []
    · case pos => subst h; grind only
    · case neg =>
      simp only [prefix_free', prefix_free, Set.mem_range,
        BinStr.proper_prefix, ne_eq, not_exists, not_and, Decidable.not_not,
        forall_exists_index, forall_apply_eq_imp_iff] at pf
      grind only
  · case mpr =>
    intro h
    constructor
    · case injective =>
      intros x y heq;
      by_contra hne
      have h1 : c x ⋢ c y := h x y hne
      have h2 : c x ⊑ c y := ⟨[], by grind only⟩
      contradiction
    · case prefix_free =>
      simp only [prefix_free', prefix_free, Set.mem_range, BinStr.proper_prefix,
        forall_exists_index]
      rintro cx x hx cy y hy ⟨z, hz1, hz2⟩
      by_cases hxy : x = y
      · case pos =>
        subst hxy;
        rw [← hx, ← hy] at hz1
        simp only [List.append_right_eq_self] at hz1
        contradiction
      · case neg =>
        have h1 : c x ⋢ c y := h x y hxy
        rw [hx, hy] at h1
        have h2 : cx ⊑ cy := ⟨z, hz1⟩
        contradiction

-------------------------------------------------------------------------------
-- Hutter's Infinite Family of Prefix Codes, E_i
-------------------------------------------------------------------------------

/--
The infinite family of prefix codes E_i : B∗→B∗, for i ∈ N, is defined as follows:
-/
@[simp]
def E : Nat -> 𝔹* -> 𝔹*
| 0, x => [true] ^ ⌜x⌝⁻¹ ++ [false]
| i + 1, x => E i ⌜ℓ x⌝ ++ x

lemma E_zero_len (x : 𝔹*) : (E 0 x).length = ⌜x⌝⁻¹ + 1 := by
  simp_all only [E, BinStr.to_nat, List.length_append,
    list_pow_eq_replicate, List.length_replicate, List.length_cons,
    List.length_nil, zero_add]

-- E_0 is injective
lemma E_0_injective : Function.Injective (E 0) := by
  simp only [Function.Injective, E, List.append_cancel_right_eq,
    list_pow_eq_replicate, List.replicate_inj, or_true, and_true]
  intros x y
  apply b0_to_nat_bijective.left

-- The range of E_0 is prefix-free
lemma E_0_prefix_free : prefix_free' (E 0) := by
  simp only [prefix_free', prefix_free, E, Set.range, Set.mem_setOf_eq,
    BinStr.proper_prefix, ne_eq, not_exists, not_and, Decidable.not_not,
    forall_exists_index, forall_apply_eq_imp_iff, List.append_assoc,
    List.cons_append, List.nil_append]
  intros x y z H
  by_cases H2 : x = y
  · case pos =>
    subst H2
    simp_all only [BinStr.to_nat, List.append_cancel_left_eq, List.cons.injEq,
      true_and]
  · case neg =>
    have : BinStr.to_nat x ≠ BinStr.to_nat y := by
      contrapose! H2
      apply b0_to_nat_bijective.left
      exact H2
    contrapose! H
    apply first_zero_neq
    rw [list_pow_eq_replicate, first_zero_replicate, list_pow_eq_replicate,
      first_zero_replicate]
    exact this

lemma PrefixCode_E_0 : PrefixCode (E 0) := by
  constructor
  · case injective => exact E_0_injective
  · case prefix_free => exact E_0_prefix_free

lemma PrefixCode_E_succ (i : Nat) (ih : PrefixCode (E i)) :
PrefixCode (E (i + 1)) := by
  rw [PrefixCode_pairwise]
  intro x y hne
  have : x ≠ y := hne
  show E (i + 1) x ⋢ E (i + 1) y
  have s1 : E (i + 1) x = E i ⌜ℓ x⌝ ++ x := E.eq_def (i + 1) x
  have s2 : E (i + 1) y = E i ⌜ℓ y⌝ ++ y := E.eq_def (i + 1) y
  by_cases h_len : ℓ x = ℓ y
  · case pos =>
      have : ⌜ℓ x⌝ = ⌜ℓ y⌝ := by grind only
      have : E i ⌜ℓ x⌝ = E i ⌜ℓ y⌝ := by grind only
      have : x ⋢ y := by grind only [prefix_and_length_eq_implies_eq]
      have : E i ⌜ℓ x⌝ ++ x ⋢ E i ⌜ℓ y⌝ ++ y := by
        grind only [prefix_with_shared_prefix]
      have : E (i + 1) x ⋢ E (i + 1) y := by grind only
      exact this
  · case neg =>
      have : ⌜ℓ x⌝ ≠ ⌜ℓ y⌝ := by grind only [nat_to_b0_injective]
      have ih_pair := PrefixCode_pairwise (E i)
      have : ∀ a b, a ≠ b → E i a ⋢ E i b := by grind only
      have : E i ⌜ℓ y⌝ ⋢ E i ⌜ℓ x⌝ := by grind only
      have : E i ⌜ℓ x⌝ ++ x ⋢ E i ⌜ℓ y⌝ ++ y := by
        grind only [prefix_incomparable_append]
      have : E (i + 1) x ⋢ E (i + 1) y := by grind only
      exact this

/--
Lemma 2.1.6 from the book
-/
theorem PrefixCode_E_i (i : Nat) : PrefixCode (E i) := by
  induction i with
  | zero => exact PrefixCode_E_0
  | succ i' ih => exact PrefixCode_E_succ i' ih

-- Theorem 2.1.7 from the book
theorem prepend_prefix_code_injective
{c : 𝔹* → 𝔹*} (h : PrefixCode c) (x1 y1 x2 y2 : 𝔹*) :
c x1 ++ y1 = c x2 ++ y2 → x1 = x2 ∧ y1 = y2 := by
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
    have s1 : c x1 ⋢ c x2 := by grind only
    have s1 : c x2 ⋢ c x1 := by grind only
    have : c x1 ++ y1 ⋢ c x2 ++ y2 := by grind [prefix_incomparable_append]
    have : c x1 ++ y1 ≠ c x2 ++ y2 := by grind [prefix_refl]
    exact this
  · next h2 =>
    have s1 : x1 = x2 ∧ y1 ≠ y2 := h2
    have : c x1 = c x2 := by grind only
    have : c x1 ++ y1 ≠ c x2 ++ y2 := by grind only [List.append_cancel_left_eq]
    exact this
