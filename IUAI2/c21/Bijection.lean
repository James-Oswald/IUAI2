import IUAI2.c21.BinStr
import Mathlib

universe u

variable (x y z : BinStr)
variable (a b c : Bool)
variable (n m l : Nat)

---- Defining Bijection ----

@[grind, aesop safe]
def nat_to_l1 (n : Nat) : BinStr :=
  -- 1-based little-endian encoding with implicit 1.  This is a bijection from ℕ⁺ to 𝔹*, as proven
    -- in theorem `nat_to_l1_to_nat`.
  -- While the book's theorems are ultimately about a 0-based big-endian encoding with an implicit,
    -- this 1-based little-endian encoding is simpler to work with, so we prove results for this
    -- encoding and then transfer the results to the book's encoding with little complication.
  match _ : n with
  | 0 => []
  | 1 => []
  | _ + 2 =>
    match n % 2 with
    | 0 => false :: nat_to_l1 (n / 2)
    | _ => true :: nat_to_l1 (n / 2)

@[grind, aesop safe]
def l1_to_nat : BinStr → Nat
  -- 1-based little-endian decoding with implicit 1.
| List.nil => 1
| false :: x' => 2 * (l1_to_nat x')
| true :: x' => 2 * (l1_to_nat x') + 1

@[grind, simp, aesop safe]
def nat_to_b0 (n : Nat) : BinStr :=
  -- 0-based big-endian encoding with implicit 1.
  -- See theorem `nat_to_b0_is_canonical_bijection` for proof of equivalence to the book's
    -- canonical bijection from 𝔹* to ℕ₀.  The advantage of starting with this definition instead
    -- of the book's definition for our proofs is that this definition (or more precisely,
    -- nat_to_l1) is recursive and thus lends itself simply to induction.
  List.reverse (nat_to_l1 (n + 1))

@[grind, simp, aesop safe]
def b0_to_nat (x : BinStr) : Nat :=
  -- 0-based big-endian decoding with implicit 1.
  -- See theorem `nat_to_b0_is_canonical_bijection_inverse` for proof of equivalence to the book's
    -- canonical bijection inverse from 𝔹* to ℕ₀.
  l1_to_nat (List.reverse x) - 1


---- Proving Bijection ----

@[grind, aesop safe]
lemma l1_to_nat_ne_0 : l1_to_nat x ≠ 0 := by
  induction x <;> grind [l1_to_nat.eq_def]

@[grind, simp, aesop unsafe]
lemma nat_to_l1_to_nat (n : Nat) (h : n ≠ 0) : l1_to_nat (nat_to_l1 n) = n := by
  -- 1-based little-endian decoding is left-inverse of respective encoding.
  match mh1: n with
  | 0 => simp_all
  | 1 => simp [nat_to_l1, l1_to_nat]
  | n'' + 2 =>
    have r1 := nat_to_l1_to_nat (n / 2)
    grind

@[grind, simp, aesop safe]
lemma l1_to_nat_to_l1 : nat_to_l1 (l1_to_nat x) = x := by
  -- 1-based little-endian decoding is right-inverse of respective encoding.
  induction x with
  | nil => simp [nat_to_l1, l1_to_nat]
  | cons a x' ih =>
    cases a
    · rw [nat_to_l1.eq_def]
      grind
    · rw [nat_to_l1.eq_def]
      grind

@[grind, simp, aesop safe]
theorem nat_to_b0_to_nat : b0_to_nat (nat_to_b0 n) = n := by
  -- 0-based big-endian decoding is left-inverse of respective encoding.
  -- This, together with `b0_to_nat_to_b0`, `nat_to_b0_is_canonical_bijection`, and
  -- `nat_to_b0_is_canonical_bijection_inverse`, show that the canonical bijection is really a
  -- bijection and that the canonical bijection inverse is really its inverse (part of Propositions
  -- 2.1.1 and 2.1.2).
  simp [nat_to_l1_to_nat]

@[grind, simp, aesop safe]
theorem b0_to_nat_to_b0 : nat_to_b0 (b0_to_nat x) = x := by
  -- 0-based big-endian decoding is right-inverse of respective encoding.
  grind [l1_to_nat_to_l1]


---- Defining Encoded Length ----

@[grind, simp, aesop safe]
def nat_l1_length (n : Nat) : Nat :=
  List.length (nat_to_l1 n)

@[grind, simp, aesop safe]
def nat_b0_length (n : Nat) : Nat :=
  List.length (nat_to_b0 n)

---- Proving Length Formulae ----


@[grind, simp, aesop unsafe]
lemma nat_l1_length_formula (n : Nat) (h : n ≠ 0) : nat_l1_length n = Nat.log2 n := by
  -- Formula for length of the 1-based little-endian encoding of a number.
  match mh1: n with
  | 0 => simp [nat_to_l1]
  | 1 => simp [Nat.log2_def, nat_to_l1]
  | n'' + 2 =>
    have r1 := nat_l1_length_formula (n / 2)
    rw [nat_l1_length]
    match mh2: n'' % 2 with
    | 0 =>
      grind [Nat.log2_def]
    | _ =>
      grind [Nat.log2_def]

@[grind, simp, aesop safe]
theorem nat_b0_length_formula (n : Nat) : nat_b0_length n = Nat.log2 (n + 1) := by
  -- Formula for the length of the 0-based big-endian encoding of a number.
    -- Arguably part of proposition 2.1.1.
  rw [← nat_l1_length_formula _ (by simp)]
  simp


---- Proving Equivalence with Book Definition ----

lemma l1_indexing_formula_helper (x : BinStr) (idx : Fin x.length) :
    (x[idx] = (l1_to_nat x / 2^idx.val % 2 == 1)) := by
  -- Formula for the bit at an index of a string in terms of the number it would represent as a
    -- 1-based little-endian encoding.
  let i := idx.val
  induction x with
  | nil => grind
  | cons a x' ih =>
    let x := a :: x'
    match mh1: i with
    | 0 =>
      grind
    | i' + 1 =>
      have ih_instantiated := ih ⟨i', by grind⟩
      have h_l1_tail_to_nat : l1_to_nat x' = l1_to_nat (a :: x') / 2 := by
        match mh2: a with
          | false => simp [l1_to_nat]
          | true => grind
      grind [Nat.div_div_eq_div_mul]

lemma l1_indexing_formula (n : Nat) (idx : Fin (nat_to_l1 n).length) :
    ((nat_to_l1 n)[idx] = (n / 2^idx.val % 2 == 1)) := by
  -- Formula for the bit at an index of the 1-based little-endian encoding of a number.
  have s1 := l1_indexing_formula_helper (nat_to_l1 n) idx
  rw [nat_to_l1_to_nat _ (by grind)] at s1
  exact s1

@[grind, simp, aesop safe]
def snoc {α : Type u} (ls : List α) (el : α) : List α :=
  ls ++ [el]

lemma l1_value_formula (x : List Bool) :
    l1_to_nat x = ∑ i : Fin (x.length + 1), (snoc x true)[i].toNat * 2 ^ i.val := by
  -- Formula for the value that a binary string represents when interpreted as 1-based
    -- little-endian.
  induction x with
  | nil =>
    simp [l1_to_nat, snoc]
  | cons a x' ih =>

    simp only [snoc]

    simp only [List.cons_append]
    simp only [Fin.sum_univ_succ]

    have h_factor : ∑ i : Fin (x'.length + 1), (x' ++ [true])[i].toNat * 2 ^ (i.val + 1) =
                       2 * ∑ i : Fin (x'.length + 1), (x' ++ [true])[i].toNat * 2 ^ i.val := by
      rw [Finset.mul_sum]
      grind

    suffices l1_to_nat (a :: x') = a.toNat + 2 * l1_to_nat x' by grind

    cases a <;> simp [l1_to_nat, Bool.toNat]; omega


lemma b0_indexing_formula_lemma (x : BinStr) (idx : Fin x.length) :
    (x[idx] = ((b0_to_nat x + 1) / 2^(x.length - 1 - idx.val) % 2 == 1)) := by

  -- Formula for the bit at an index of the 0-based big-endian encoding of a number.

  rw [b0_to_nat]

  have s1 : (l1_to_nat x.reverse) ≠ 0 := by
    induction x.reverse <;> simp [l1_to_nat_ne_0]

  suffices x[idx] = ((l1_to_nat (List.reverse x)) / 2 ^ (List.length x - 1 - idx) % 2 == 1) by
    grind

  have s2 : x[idx] = (x.reverse)[x.reverse.length - 1 - idx]'(by grind) := by grind
  rw [s2]

  have h := l1_indexing_formula_helper x.reverse ⟨x.reverse.length - 1 - idx, by grind⟩

  simp_all


lemma b0_indexing_formula (n : Nat) (idx : Fin (nat_to_b0 n).length) :
    (nat_to_b0 n)[idx] = ((n + 1) / 2^((nat_to_b0 n).length - 1 - idx.val) % 2 == 1) := by
  -- Formula for the bit at an index of the 1-based little-endian encoding of a number.
  have s1 := b0_indexing_formula_lemma (nat_to_b0 n) idx

  rw [nat_to_b0_to_nat _] at s1
  exact s1

def B (n : Nat) : BinStr :=
  -- 0-based big-endian encoding *without* implicit 1, defined in accordance with the book.
  let l := Nat.log2 n + 1
  List.map (λ i => (n / 2 ^ (l - i)) % 2 == 1) (List.range' 1 l)
    -- While the book writes (n + 1) instead of n when defining l, it is clear from the context
    -- that the n there refers to the n from the canonical bijection formula rather than the n
    -- from the defininition of B.

lemma b0_value_formula :
    b0_to_nat x = (∑ i : Fin (x.length + 1), (true :: x)[i].toNat * 2 ^ (x.length - i)) - 1 := by
  -- Formula for the bit at an index of the 0-based big-endian encoding (with implicit 1) of
    -- a number.
  rw [b0_to_nat]
  congr 1
  rw [l1_value_formula]

  refine Finset.sum_bij (fun i _ => ⟨x.length - i.val, ?_⟩) ?_ ?_ ?_ ?_
  · simp
  · simp
  · grind
  · intro b _
    use ⟨x.length - b.val, by simp⟩
    grind
  grind


theorem nat_to_b0_is_canonical_bijection : nat_to_b0 n = (B (n + 1)).tail := by
  -- The 0-based big-endian encoding `nat_to_b0` is, in fact, the canonical bijection from ℕ → 𝔹*
    -- defined in the book in Proposition 2.1.1.
  let a1 := nat_to_b0 n
  let a2 := (B (n + 1)).tail
  have h_length_eq: a1.length = a2.length := by
    have s1 : a1.length = (n + 1).log2 := by
      unfold a1
      rw [← nat_b0_length]
      exact nat_b0_length_formula n
    suffices a2.length = (n + 1).log2 by
      rw [s1, this]
    unfold a2
    rw [List.length_tail]
    rw [B]
    rw [List.length_map]
    simp
  suffices ∀ i : Fin (a1.length), a1[i] = a2[i] by
    refine List.ext_get h_length_eq ?_
    intro i h_1 h_2
    have thing := this ⟨i, by grind⟩
    grind
  intro i
  unfold a1
  rw [b0_indexing_formula_lemma]
  rw [nat_to_b0_to_nat]
  have : List.length (nat_to_b0 n) = nat_b0_length n := by
    rw [← nat_b0_length]
  suffices ((n + 1) / 2 ^ (nat_b0_length n - 1 - ↑i) % 2 == 1) = a2[i] by
    -- this `suffices` is needed instead of a direct `rw` due to motive issues
    rw [nat_b0_length] at this
    exact this
  rw [nat_b0_length_formula]
  unfold a2
  unfold B
  grind

theorem b0_to_nat_is_canonical_bijection_inverse :
    b0_to_nat x = (∑ i : Fin (x.length + 1), (true :: x)[i].toNat * 2 ^ (x.length - i)) - 1 := by
  -- The 0-based big-endian decoding `b0_to_nat` is, in fact, the canonical bijection inverse from
    -- ℕ → 𝔹* defined in the book by Proposition 2.1.2.
  exact b0_value_formula x

---- Bijection Length Bound ----


lemma l1_length_bound (x : BinStr) :
    2^x.length ≤ l1_to_nat x ∧ l1_to_nat x ≤ 2^(x.length + 1) - 1 := by
  -- Bounds, in terms of the string's length, on the value of a number represented by a binary
    -- string interpreted in 1-based little-endian.
  let n := l1_to_nat x
  suffices  2^(nat_to_l1 n).length ≤ l1_to_nat (nat_to_l1 n) ∧
    l1_to_nat (nat_to_l1 n) ≤ 2^((nat_to_l1 n).length + 1) - 1 by grind

  rw [← nat_l1_length]
  rw [nat_l1_length_formula _ (by grind)]
  have n_ne_0 : n ≠ 0 := by exact l1_to_nat_ne_0 _
  rw [nat_to_l1_to_nat _ n_ne_0]

  have : 2 ^ n.log2 ≤ n := by simp [Nat.pow_log_le_self 2 n_ne_0, Nat.log2_eq_log_two]

  refine ⟨this, ?_⟩

  rw [Nat.log2_eq_log_two]
  rw [← Nat.succ_eq_add_one]

  suffices n < 2 ^ (Nat.log 2 n).succ by grind
  exact Nat.lt_pow_succ_log_self (by simp) n


theorem b0_length_bound (x : BinStr) :
    2^x.length - 1 ≤ b0_to_nat x ∧ b0_to_nat x ≤ 2^(x.length + 1) - 2 := by
  -- Bounds, in terms of the string's length, on the value of a number encoded through the
    -- canonical bijection.
  -- Proposition 2.1.3.
  rw [b0_to_nat]
  rw [← List.length_reverse]
  grind [l1_length_bound]

---- Setup and Proof of Length-Lexicographicality of Canonical Bijection ----


@[grind, aesop safe]
def l1_succ (x : BinStr) :=
  match x with
  | [] => [false]
  | false :: x' => true :: x'
  | true :: x' => false :: l1_succ x'

@[grind, simp, aesop safe]
lemma l1_to_nat_preserves_succ : l1_to_nat (l1_succ x) = (l1_to_nat x).succ := by
  induction x with
  | nil => simp [l1_to_nat, l1_succ]
  | cons a x' =>
    rw [l1_succ.eq_def]
    rw [l1_to_nat.eq_def]
    grind

@[grind, aesop safe]
def same_length_lex : BinStr → BinStr → Bool
-- Lexicographical order for binary strings of the same length.
| [], [] => false
| a :: xs, b :: ys =>
    if a != b then !a && b
    else same_length_lex xs ys
| _, _ => false

@[simp, grind, aesop safe]
def llex (x y : BinStr) : Bool :=
  -- Length-lexicographical order.
  x.length < y.length || (x.length == y.length && same_length_lex x y)

@[simp, grind, aesop safe]
def bool_compareTo : Bool → Bool → SignType
| false, true => -1
| false, false => 0
| true, true => 0
| true, false => 1

@[grind, aesop unsafe]
def length_colex_compareTo : BinStr → BinStr → SignType
-- Returns -1, 0, or 1 if the first argument is respectively less than, equal to, or greater than
  -- the second argument in length-colexicographical order (i.e. where comparison begins from the
  -- right side of the string).
| [], [] => 0
| [], _ => -1
| _, [] => 1
| a :: x', b :: y' =>
  let tail_result := length_colex_compareTo x' y'
  if tail_result ≠ 0 then tail_result else bool_compareTo a b

@[simp, grind, aesop safe]
def lcolex (x y : BinStr) : Bool :=
  -- "Less than" in length-colexicographical order (i.e. where comparison begins from the right
    -- side of the string).
  -- This is convenient because a direct, cons-based definition of colexicographical order can be
    -- given that matches on the same side of the string that `l1_succ` matches on (the left),
    -- simplifying proofs significantly.
  length_colex_compareTo x y == -1


@[grind, aesop unsafe]
lemma lcolex_compareTo_diff_length :
    x.length ≠ y.length →
    length_colex_compareTo x y = if x.length < y.length then -1 else 1 := by
  intro h
  induction x generalizing y with
  | nil =>
    cases y with
    | nil =>
      simp at h
    | cons b ys =>
      simp [length_colex_compareTo]
  | cons a xs ih =>
    cases y with
    | nil =>
      simp [length_colex_compareTo]
    | cons b ys =>
      have h' : xs.length ≠ ys.length := by simp at h; omega
      have ih_applied := ih ys h'
      rw [length_colex_compareTo]
      simp [ih_applied]
      grind [SignType.neg_eq_zero_iff]

@[grind, aesop unsafe]
lemma llex_colex_reverse_diff_length :
    x.length ≠ y.length → llex x y = lcolex x.reverse y.reverse := by
  intro h
  rw [llex]
  have h_eq_false : (x.length == y.length) = false := by simp [h]
  simp [h_eq_false]
  suffices (x.length < y.length) = (length_colex_compareTo x.reverse y.reverse == -1) by grind
  have h_rev : x.reverse.length ≠ y.reverse.length := by simp [h]
  rw [lcolex_compareTo_diff_length _ _ h_rev]
  simp_all

@[grind, aesop unsafe]
lemma lcolex_compareTo_append_same_length :
    x.length = y.length →
    length_colex_compareTo (x ++ [a]) (y ++ [b]) =
    let last_result := bool_compareTo a b
    if last_result ≠ 0 then last_result else length_colex_compareTo x y := by

  intro h
  induction x generalizing y with
  | nil =>
    cases y with
    | nil =>
      simp [length_colex_compareTo]
    | cons c zs =>
      simp at h
  | cons c zs ih =>
    cases y with
    | nil =>
      simp at h
    | cons d ws =>
      simp at h
      simp [length_colex_compareTo]
      have ih_applied := ih ws h
      rw [ih_applied]
      simp
      split
      · rfl
      · rfl
      grind
      grind

@[grind, aesop unsafe]
lemma llex_colex_reverse_same_length :
    x.length = y.length → llex x y = lcolex x.reverse y.reverse := by
  intro h
  rw [llex, lcolex]
  have h_eq_true : (x.length == y.length) = true := by simp [h]
  have h_lt_false : (x.length < y.length) = false := by grind
  simp [h_eq_true, h_lt_false]
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b ys => simp at h
  | cons a xs ih =>
    cases y with
    | nil => simp at h
    | cons b ys =>
      simp at h
      have h_xs_eq : (xs.length == ys.length) = true := by simp [h]
      have h_xs_lt : (xs.length < ys.length) = false := by grind
      have ih_applied := ih ys h h_xs_eq h_xs_lt
      simp [same_length_lex]
      have h_rev_len : xs.reverse.length = ys.reverse.length := by simp [h]
      rw [lcolex_compareTo_append_same_length _ _]
      simp
      cases a <;> cases b <;> simp [ih_applied]
      grind


lemma nat_to_l1_is_length_colexicographical_when_diff_length :
    n ≠ 0 ∧ m ≠ 0 ∧ n < m ∧ (nat_to_l1 n).length ≠ (nat_to_l1 m).length →
    lcolex (nat_to_l1 n) (nat_to_l1 m) := by
  intro ⟨hn_ne_0, hm_ne_0, hn_lt_m, hlen_ne⟩
  rw [lcolex]
  rw [lcolex_compareTo_diff_length _ _ hlen_ne]
  have hn_len : (nat_to_l1 n).length = Nat.log2 n := by
    rw [← nat_l1_length]
    exact nat_l1_length_formula n hn_ne_0
  have hm_len : (nat_to_l1 m).length = Nat.log2 m := by
    rw [← nat_l1_length]
    exact nat_l1_length_formula m hm_ne_0
  rw [hn_len, hm_len]
  have hlog_le : Nat.log2 n ≤ Nat.log2 m := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.le_of_lt hn_lt_m)
  have hlog_ne : Nat.log2 n ≠ Nat.log2 m := by
    rw [← hn_len, ← hm_len]
    exact hlen_ne
  have hlog_lt : Nat.log2 n < Nat.log2 m := by
    omega
  simp [hlog_lt]

@[simp, grind, aesop safe]
lemma lcolex_compareTo_refl (x : BinStr) :
    length_colex_compareTo x x = 0 := by
  induction x with
  | nil =>
    rfl
  | cons a xs ih =>
    rw [length_colex_compareTo]
    simp [ih]
    cases a <;> rfl

@[grind, aesop safe]
lemma lcolex_l1_succ (x : BinStr) :
    lcolex x (l1_succ x) := by
  induction x with
  | nil =>
    rw [lcolex]
    rw [length_colex_compareTo]
    rfl
    grind
  | cons a xs ih =>
    cases a
    · rw [l1_succ]
      rw [lcolex]
      rw [length_colex_compareTo]
      simp [bool_compareTo]
    · rw [l1_succ]
      rw [lcolex]
      rw [length_colex_compareTo]
      have ih_eq : length_colex_compareTo xs (l1_succ xs) == -1 := by grind
      simp_all

@[grind, aesop unsafe]
lemma nat_to_l1_llex_nat_to_l1_succ :
    n ≠ 0 → lcolex (nat_to_l1 n) (nat_to_l1 n.succ) := by
  intro hn
  have h_succ : nat_to_l1 n.succ = l1_succ (nat_to_l1 n) := by
    have : l1_to_nat (l1_succ (nat_to_l1 n)) = n.succ := by
      rw [l1_to_nat_preserves_succ]
      rw [nat_to_l1_to_nat n hn]
    have : nat_to_l1 (l1_to_nat (l1_succ (nat_to_l1 n))) = l1_succ (nat_to_l1 n) := by grind
    rw [← this]
    simp [l1_to_nat_preserves_succ, nat_to_l1_to_nat n hn]
  rw [h_succ]
  exact lcolex_l1_succ (nat_to_l1 n)

@[simp, grind]
lemma lcolex_compareTo_eq_zero_iff :
    length_colex_compareTo x y = 0 ↔ x = y := by
  constructor
  · intro h
    induction x generalizing y with
    | nil =>
      cases y with
      | nil =>
        rfl
      | cons b ys =>
        simp [length_colex_compareTo] at h
    | cons a xs ih =>
      cases y with
      | nil =>
        simp [length_colex_compareTo] at h
      | cons b ys =>
        rw [length_colex_compareTo] at h
        split at h
        · contradiction
        · have xs_eq_ys := ih ys (by grind)
          have a_eq_b : a = b := by
            cases a <;> cases b <;> simp at h <;> rfl
          rw [xs_eq_ys, a_eq_b]
  · intro h
    rw [h]
    exact lcolex_compareTo_refl y

@[grind, aesop safe]
lemma lcolex_compareTo_trans_neg :
    length_colex_compareTo x y = -1 →
    length_colex_compareTo y z = -1 →
    length_colex_compareTo x z = -1 := by
  intro hab hbc
  induction x generalizing y z with
  | nil =>
    cases z with
    | nil =>
      cases y with
      | nil => simp at hab
      | cons b ys => simp [lcolex_compareTo_diff_length] at hbc
    | cons c zs =>
      rfl
  | cons a xs ih =>
    cases y with
    | nil => simp [lcolex_compareTo_diff_length] at hab
    | cons b ys =>
      cases z with
      | nil => grind
      | cons c zs =>
        rw [length_colex_compareTo] at hab hbc ⊢
        split at hab
        · split at hbc <;> grind
        · split at hbc
          · grind
          · split
            · grind
            · cases a <;> cases b <;> cases c <;> simp at hab hbc ⊢

@[grind, aesop safe]
lemma lcolex_trans :
    lcolex x y → lcolex y z → lcolex x z := by
  grind

lemma nat_to_l1_is_length_colexicographical_when_same_length :
    n ≠ 0 ∧ n < m ∧ (nat_to_l1 n).length = (nat_to_l1 m).length →
    lcolex (nat_to_l1 n) (nat_to_l1 m) := by
  intro ⟨hn_ne_0, hn_lt_m, hlen_eq⟩

  have : ∀ k, ∀ n m, n ≠ 0 → n < m → (nat_to_l1 n).length = (nat_to_l1 m).length →
         m - n = k → lcolex (nat_to_l1 n) (nat_to_l1 m) := by
    intro k
    induction k with
    | zero => grind
    | succ k' ih =>
      intro n m hn_ne_0 hn_lt_m hlen_eq hk
      by_cases h : m = n.succ
      · rw [h]
        exact nat_to_l1_llex_nat_to_l1_succ n hn_ne_0
      · have hn_succ_lt_m : n.succ < m := by omega
        have hn_succ_ne_0 : n.succ ≠ 0 := by omega
        have hlen_n_succ : (nat_to_l1 n.succ).length = (nat_to_l1 m).length := by
          rw [← nat_l1_length, nat_l1_length_formula n hn_ne_0] at hlen_eq
          rw [← nat_l1_length, nat_l1_length_formula m (by omega)] at hlen_eq
          rw [← nat_l1_length, nat_l1_length_formula n.succ hn_succ_ne_0]
          rw [← nat_l1_length, nat_l1_length_formula m (by omega)]
          have h1 : Nat.log2 n ≤ Nat.log2 n.succ := by
            rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
            exact Nat.log_mono_right (Nat.le_succ n)
          have h2 : Nat.log2 n.succ ≤ Nat.log2 m := by
            rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
            exact Nat.log_mono_right (Nat.le_of_lt hn_succ_lt_m)
          omega
        have h_diff : m - n.succ = k' := by omega
        have ih_applied := ih n.succ m hn_succ_ne_0 hn_succ_lt_m hlen_n_succ h_diff
        have h1 := nat_to_l1_llex_nat_to_l1_succ n hn_ne_0
        exact lcolex_trans (nat_to_l1 n) (nat_to_l1 n.succ) (nat_to_l1 m) h1 ih_applied

  exact this (m - n) n m hn_ne_0 hn_lt_m hlen_eq rfl

@[grind, aesop safe]
lemma nat_to_l1_is_length_colexicographical :
    n ≠ 0 ∧ n < m → lcolex (nat_to_l1 n) (nat_to_l1 m) := by
  grind [nat_to_l1_is_length_colexicographical_when_same_length,
    nat_to_l1_is_length_colexicographical_when_diff_length]

@[grind, aesop unsafe]
theorem nat_to_b0_is_length_lexicographical : n < m → llex (nat_to_b0 n) (nat_to_b0 m) := by
  -- The canonical bijection from ℕ to 𝔹* orders the binary strings length-lexicographically.
  -- Part of Proposition 2.1.1.
  grind


lemma same_length_llex_iff_lex (x y : BinStr) (h : x.length = y.length) :
    same_length_lex x y = true ↔ List.Lex (· < ·) x y := by
  induction x generalizing y with
  | nil =>
    cases y <;> simp [same_length_lex] at h ⊢
  | cons a xs ih =>
    cases y with
    | nil => grind
    | cons b ys =>
      rw [same_length_lex]
      rw [List.length_cons] at h
      by_cases hxy : a = b
      · simp_all
      · simp only [hxy, ite_true, bne_iff_ne, ne_eq, not_false_eq_true]
        constructor
        · intro h_and
          have : a = false ∧ b = true := by grind
          rw [this.1, this.2]
          exact List.Lex.rel (by decide : false < true)
        · intro h_lex
          cases h_lex with
          | cons h_tail => contradiction
          | rel h_rel =>
            cases a <;> cases b
            · simp at h_rel
            · simp
            · have : ¬(true < false) := by decide
              contradiction
            · simp at h_rel

theorem length_llex_iff_shortlex (x y : BinStr) :
    llex x y = true ↔ List.Shortlex (· < ·) x y := by
  -- llex is (a computational) equivalent to List.Shortlex.
  unfold llex List.Shortlex InvImage
  grind [same_length_llex_iff_lex]

---- Proofs of some additional results for succ and pred on binary strings ----

@[grind, simp, aesop safe]
def b0_succ (x : BinStr) :=
  (l1_succ x.reverse).reverse

@[grind, simp, aesop safe]
lemma b0_to_nat_preserves_succ : b0_to_nat (b0_succ x) = (b0_to_nat x).succ := by
  grind

@[grind, aesop safe]
def l1_pred (x : BinStr) :=
  match x with
  | [] => []
  | [false] => []
  | true :: x' => false :: x'
  | false :: x' => true :: l1_pred x'

@[grind, simp, aesop safe]
def b0_pred (x : BinStr) :=
  (l1_pred x.reverse).reverse

@[grind, simp, aesop safe]
lemma l1_pred_l1_succ (x : BinStr): l1_pred (l1_succ x) = x := by
  induction x with
  | nil => simp [l1_succ, l1_pred]
  | cons a x' ih =>
    rw [l1_succ.eq_def]
    cases a
    · simp [l1_pred]
    · grind

@[grind, simp, aesop safe]
lemma b0_pred_b0_succ (x : BinStr) : b0_pred (b0_succ x) = x := by
  simp

@[grind, simp, aesop unsafe]
lemma l1_succ_l1_pred (x : BinStr): x ≠ [] → l1_succ (l1_pred x) = x := by
  induction x with
  | nil => simp
  | cons a x' ih =>

    intro h
    match mh: x' with
    | [] =>
      rw [l1_succ.eq_def]
      rw [l1_pred.eq_def]
      grind
    | b :: x'' =>
      have ih1 : l1_succ (l1_pred (b :: x'')) = b :: x'' := by simp_all
      rw [l1_pred.eq_def]
      grind

@[grind, simp, aesop unsafe]
lemma b0_succ_b0_pred (x : BinStr): x ≠ [] → b0_succ (b0_pred x) = x := by
  grind [l1_pred.eq_def, l1_succ.eq_def]


@[grind, simp, aesop unsafe]
lemma l1_to_nat_preserves_pred : x ≠ [] → l1_to_nat (l1_pred x) = (l1_to_nat x).pred := by
  intro h
  suffices (l1_to_nat (l1_pred x)).succ = l1_to_nat x by
    have s1 : (l1_to_nat x).pred.succ = l1_to_nat x := by
      rw [Nat.succ_pred (by simp [l1_to_nat_ne_0])]
    symm
    suffices (l1_to_nat (l1_pred x)).succ = (l1_to_nat x).pred.succ by grind
    suffices (l1_to_nat (l1_pred x)).succ = (l1_to_nat x) by simp_all
    rw [← l1_to_nat_preserves_succ]
    rw [l1_succ_l1_pred x (by exact h)]
  symm
  have s1 : l1_to_nat (l1_succ (l1_pred x)) = (l1_to_nat (l1_pred x)).succ := by
    refine l1_to_nat_preserves_succ ?_
  rw [l1_succ_l1_pred x h] at s1
  exact s1

@[grind, simp, aesop unsafe]
lemma b0_to_nat_preserves_pred : x ≠ [] → b0_to_nat (b0_pred x) = (b0_to_nat x).pred := by
  simp_all

---- Biblography ----

-- Hutter, M., Quarel, D., Catt, E.: An Introduction to Universal Artificial Intelligence. CRC Press, 2024 christmas edn. (2024)
