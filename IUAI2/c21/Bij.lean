
import IUAI2.c21.BinStr
import Mathlib

-- -- The binary string length of 1 + n
-- @[simp]
-- def l (n : Nat) : Nat :=
--     (Nat.log2 (n + 1)) + 1

-- -- The ith binary digit of n
-- @[simp]
-- def Bi (n i : Nat) : Nat :=
--     (n ⌊/⌋ 2^((l n) - i)) % 2

-- -- Bi only returns leq 1
-- lemma Bi_leq_1 (n i : Nat) : Bi n i ≤ 1 := by
--     simp only [Bi]
--     omega

-- lemma Bi_0_or_1 (n i : Nat) : Bi n i = 0 ∨ Bi n i = 1 := by
--     have H := Bi_leq_1 n i
--     omega

-- def Bib (n i : Nat) : Bool :=
--     if Bi n i = 1 then true else false

-- def B (s n : Nat) : BinStr :=
--     List.map (Bib n ·) (List.range s)


def bits : Nat -> BinStr
| 0 => []
| n + 1 =>
    let b := if (n + 1) % 2 = 1 then true else false
    bits ((n + 1) / 2) ++ [b]

lemma bits_leq (n : Nat) (H : n > 0) : (bits n).length ≤ (bits (n + 1)).length := by
    induction n
    . case zero => contradiction
    . case succ n ih =>
      by_cases h : n = 0
      . case pos =>
        rw [h]
        simp [bits]
      . case neg =>
        have H3: n > 0 := by omega
        have H2 : (bits n).length ≤ (bits (n + 1)).length := ih H3
        simp [bits]


example (n : Nat) (H : n > 0): (bits n).length = Nat.log2 n + 1 := by
    induction n
    . case zero => contradiction
    . case succ n ih =>
        by_cases h : n = 0
        . case pos =>
            rw [h]
            simp [bits]
            rw [Nat.log2]
            simp only [ge_iff_le, Nat.not_ofNat_le_one, ↓reduceIte]
        . case neg =>
            have H3: n > 0 := by omega
            have H2 : (bits n).length = Nat.log2 n + 1 := ih H3
            rw [Nat.log2] at H2
            rw [Nat.log2]
            by_cases h2 : n ≥ 2
            by_cases h3 : n ≤ 1
            . case pos => omega
            . case neg =>
              simp_all
              have h4 : 1 ≤ n := by omega
              simp [h4]





def cb (n : Nat) : BinStr :=
    (n + 1).bits.reverse.tail

-- example (n : Nat) : 1 < (n + 1 + 1).size := by
--     induction n using Nat.binaryRec
--     . case z => sorry
--     . case f b n ih =>
--       have H2 : 1 + 1 ≤ (n + 1 + 1).size.succ := by sorry
--       rw [<-@Nat.size_bit b _] at H2



theorem cb_injective : Function.Injective cb := by
    simp [Function.Injective]
    intro a b H
    have Hl : (cb a).length = (cb b).length := by rw [H]
    induction a
    induction b
    · case zero.zero => simp
    · case zero.succ b ih =>
      simp only [cb, zero_add, Nat.one_bits, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.tail_cons, List.length_nil, List.tail_reverse, List.length_reverse,
        List.length_dropLast, Nat.size_eq_bits_len] at Hl




abbrev v : Nat := 6
#eval l v
#eval Bi v 1
#eval B v
#eval cb v


theorem canonicalBijection : Function.Bijective cb := by
    constructor
    . case left =>
      simp [Function.Injective]
      intro a b
      sorry
    . case right =>
      sorry
