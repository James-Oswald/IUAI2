
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


def Nat.bits' : Nat -> {b : BinStr // b ≠ []}
| 0 => ⟨[false], by simp⟩
| n + 1 =>
    let b := if (n + 1) % 2 = 1 then true else false
    ⟨bits' ((n + 1) / 2) ++ [b], by simp⟩

def BinStr.nat : {b : BinStr // b ≠ []}  -> Nat
| ⟨[false], _⟩ => 0
| ⟨[true], _⟩ => 1
| ⟨h::t, H⟩ => 2^t.length * (if h then 1 else 0) + BinStr.nat ⟨t, by simp [H]⟩

def cb (n : Nat) : BinStr :=
    (n + 1).bits'.tail

def cb



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
