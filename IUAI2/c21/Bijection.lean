import IUAI2.c21.BinStr
import Mathlib

universe u

variable (x y z : 𝔹*)
variable (a b c : Bool)
variable (n m l : Nat)

---- Defining Bijection ----

@[grind, aesop safe, simp]
def nat_to_l1 (n : Nat) : 𝔹* :=
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

@[grind, aesop safe, simp]
def l1_to_nat : 𝔹* → Nat
  -- 1-based little-endian decoding with implicit 1.
| List.nil => 1
| false :: x' => 2 * (l1_to_nat x')
| true :: x' => 2 * (l1_to_nat x') + 1

@[grind, simp, aesop safe]
def nat_to_b0 (n : Nat) : 𝔹* :=
  -- 0-based big-endian encoding with implicit 1.
  -- See theorem `nat_to_b0_is_canonical_bijection` for proof of equivalence to the book's
    -- canonical bijection from 𝔹* to ℕ₀.  The advantage of starting with this definition instead
    -- of the book's definition for our proofs is that this definition (or more precisely,
    -- nat_to_l1) is recursive and thus lends itself simply to induction.
  List.reverse (nat_to_l1 (n + 1))

@[grind, simp, aesop safe]
def b0_to_nat (x : 𝔹*) : Nat :=
  -- 0-based big-endian decoding with implicit 1.
  -- See theorem `nat_to_b0_is_canonical_bijection_inverse` for proof of equivalence to the book's
    -- canonical bijection inverse from 𝔹* to ℕ₀.
  l1_to_nat (List.reverse x) - 1


---- Proving Bijection ----

@[grind ., aesop safe]
lemma l1_to_nat_ne_0 : l1_to_nat x ≠ 0 := by
  induction x <;> grind [l1_to_nat.eq_def]

@[grind =, simp, aesop unsafe]
lemma nat_to_l1_to_nat (n : Nat) (h : n ≠ 0) : l1_to_nat (nat_to_l1 n) = n := by
  -- 1-based little-endian decoding is left-inverse of respective encoding.
  match mh1: n with
  | 0 => simp_all
  | 1 => simp [nat_to_l1, l1_to_nat]
  | n'' + 2 =>
    have r1 := nat_to_l1_to_nat (n / 2)
    grind only [nat_to_l1, l1_to_nat, #4565, #c576]

@[grind =, simp, aesop safe]
lemma l1_to_nat_to_l1 : nat_to_l1 (l1_to_nat x) = x := by
  -- 1-based little-endian decoding is right-inverse of respective encoding.
  induction x with
  | nil => simp [nat_to_l1, l1_to_nat]
  | cons a x' ih =>
    cases a
    · rw [nat_to_l1.eq_def]
      grind only [l1_to_nat_ne_0, l1_to_nat, #0b64, #ef08, #2841]
    · rw [nat_to_l1.eq_def]
      grind only [l1_to_nat_ne_0, l1_to_nat, #c4c9, #dac0, #9f1a]

@[grind =, simp, aesop safe]
theorem nat_to_b0_to_nat : b0_to_nat (nat_to_b0 n) = n := by
  -- 0-based big-endian decoding is left-inverse of respective encoding.
  -- This, together with `b0_to_nat_to_b0`, `nat_to_b0_is_canonical_bijection`, and
  -- `nat_to_b0_is_canonical_bijection_inverse`, show that the canonical bijection is really a
  -- bijection and that the canonical bijection inverse is really its inverse (part of Propositions
  -- 2.1.1 and 2.1.2).
  simp [nat_to_l1_to_nat]

@[grind =, simp, aesop safe]
theorem b0_to_nat_to_b0 : nat_to_b0 (b0_to_nat x) = x := by
  -- 0-based big-endian decoding is right-inverse of respective encoding.
  grind [l1_to_nat_to_l1]


theorem b0_to_nat_bijective : Function.Bijective b0_to_nat := by
  apply Function.bijective_iff_has_inverse.mpr
  use nat_to_b0
  constructor
  · simp only [Function.LeftInverse]
    exact b0_to_nat_to_b0
  · simp only [Function.RightInverse]
    exact nat_to_b0_to_nat

theorem nat_to_b0_bijective : Function.Bijective nat_to_b0 := by
  apply Function.bijective_iff_has_inverse.mpr
  use b0_to_nat
  constructor
  · simp only [Function.LeftInverse]
    exact nat_to_b0_to_nat
  · simp only [Function.RightInverse]
    exact b0_to_nat_to_b0

---- Defining Encoded Length ----

@[grind, simp, aesop safe]
def nat_l1_length (n : Nat) : Nat :=
  List.length (nat_to_l1 n)

@[grind, simp, aesop safe]
def nat_b0_length (n : Nat) : Nat :=
  List.length (nat_to_b0 n)

---- Proving Length Formulae ----

@[grind =, simp, aesop unsafe]
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

@[grind =, simp, aesop safe]
theorem nat_b0_length_formula (n : Nat) : nat_b0_length n = Nat.log2 (n + 1) := by
  -- Formula for the length of the 0-based big-endian encoding of a number.
    -- Arguably part of proposition 2.1.1.
  rw [← nat_l1_length_formula _ (by simp)]
  simp


---- Proving Equivalence with Book Definition ----

lemma l1_indexing_formula_helper (x : 𝔹*) (idx : Fin x.length) :
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
      grind only [usr Fin.isLt, = Fin.getElem_fin, usr Nat.div_pow_of_pos, = List.getElem_cons,
        l1_to_nat, #c2f4]
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


lemma b0_indexing_formula_lemma (x : 𝔹*) (idx : Fin x.length) :
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

def B (n : Nat) : 𝔹* :=
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
  · simp only [Order.lt_add_one_iff, tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
  · simp only [Finset.mem_univ, imp_self, implies_true]
  · grind
  · intro b _
    use ⟨x.length - b.val, by simp⟩
    grind only [← Finset.mem_univ, = List.length_reverse, usr Fin.isLt, #bbcc]
  grind =>
    instantiate approx
    instantiate only [= Lean.Grind.toInt_fin, = List.getElem_cons, = List.length_append]
    ring
    instantiate only [= List.length_cons]
    instantiate only [= List.length_nil]
    instantiate only [= List.getElem_append]
    cases #f3b3
    · instantiate only [= List.getElem_reverse]
      cases #9d38 <;> mbtc <;> cases #e07fb3f9634c697d <;> cases #c1df
    · instantiate only [= List.getElem_cons]
      cases #9d38

-- Soundness and completeness of of our canconical bijection
-- With the textbook version, proposition 2.1.1
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

-- Soundness and completeness of of our canconical bijection
-- With the textbook version, proposition 2.1.1
theorem b0_to_nat_is_canonical_bijection_inverse :
    b0_to_nat x = (∑ i : Fin (x.length + 1), (true :: x)[i].toNat * 2 ^ (x.length - i)) - 1 := by
  -- The 0-based big-endian decoding `b0_to_nat` is, in fact, the canonical bijection inverse from
    -- ℕ → 𝔹* defined in the book by Proposition 2.1.2.
  exact b0_value_formula x

lemma l1_length_bound (x : 𝔹*) :
    2^x.length ≤ l1_to_nat x ∧ l1_to_nat x ≤ 2^(x.length + 1) - 1 := by
  -- Bounds, in terms of the string's length, on the value of a number represented by a binary
    -- string interpreted in 1-based little-endian.
  let n := l1_to_nat x
  suffices  2^(nat_to_l1 n).length ≤ l1_to_nat (nat_to_l1 n) ∧
    l1_to_nat (nat_to_l1 n) ≤ 2^((nat_to_l1 n).length + 1) - 1 by grind only [= l1_to_nat_to_l1]

  rw [← nat_l1_length]
  rw [nat_l1_length_formula _ (by grind)]
  have n_ne_0 : n ≠ 0 := by exact l1_to_nat_ne_0 _
  rw [nat_to_l1_to_nat _ n_ne_0]

  have : 2 ^ n.log2 ≤ n := by simp only [Nat.log2_eq_log_two, Nat.pow_log_le_self 2 n_ne_0]

  refine ⟨this, ?_⟩

  rw [Nat.log2_eq_log_two]
  rw [← Nat.succ_eq_add_one]

  suffices n < 2 ^ (Nat.log 2 n).succ by grind only [usr Nat.pow_pos]
  exact Nat.lt_pow_succ_log_self (by simp) n

/--
Propotion 2.1.3: Bijection Length Bound.
-/
theorem b0_length_bound (x : 𝔹*) :
    2^x.length - 1 ≤ b0_to_nat x ∧ b0_to_nat x ≤ 2^(x.length + 1) - 2 := by
  -- Bounds, in terms of the string's length, on the value of a number encoded through the
    -- canonical bijection.
  -- Proposition 2.1.3.
  rw [b0_to_nat]
  rw [← List.length_reverse]
  grind [l1_length_bound]

theorem b0_length_upper : b0_to_nat x ≤ 2^(x.length + 1) - 2 := by
  exact (b0_length_bound x).2

theorem b0_length_lower : 2^x.length - 1 ≤ b0_to_nat x := by
  exact (b0_length_bound x).1
