
import Mathlib

-- The type of finite binary strings
structure BinString where
    u: List Nat
    --u_cond: ∀e ∈ u, e ≤ 1
deriving Repr

def len (b : BinString) : Nat := b.u.length

def BinStringSet : Set BinString := Set.univ

notation "𝔹*" => BinStringSet

def BinStringSetN (n : Nat) : Set BinString :=
    { b : BinString | b.u.length = n }

prefix:max "𝔹^" => BinStringSetN

#check 𝔹^3

example : 𝔹^3 ⊆ 𝔹* := by
    simp only [BinStringSet, Set.subset_univ]

example : ∀n, 𝔹^n ⊆ 𝔹* := by
    intro n
    simp [BinStringSet]

example : (⋃ (n : Nat), 𝔹^n) = 𝔹* := by
    simp only [BinStringSet]
    apply Set.ext
    intro x
    simp_all only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exists x.u.length

-- The length of the binary representation of n
@[simp]
def l (n : Nat) : Nat :=
    (Nat.log2 n) + 1

-- The ith binary digit of n
@[simp]
def Bi (n i : Nat) : Nat :=
    (n ⌊/⌋ 2^((l n) - i)) % 2

def B (n : Nat) : BinString :=
    List.range (l n + 1) |>.tail |>.map (Bi n ·) |> BinString.mk

def ce (n : Nat) : BinString :=
    B (n + 1) |>.u.tail |> BinString.mk

abbrev v : Nat := 4
#eval l v
#eval Bi v 1
#eval B v
#eval ce v


-- The first digit of every binary number representation is 1
lemma Bi_one_one (n : Nat) (H : n > 0) : Bi n 1 = 1 := by
    simp only [Bi, l, add_tsub_cancel_right, Nat.floorDiv_eq_div]












-- lemma B_zero_one (n i: Nat) : B n i = 0 ∨ B n i = 1 := by
--     induction n
--     induction i
--     simp [B]






#check B' 1




theorem canonicalBijection : Function.Bijective ce := by
    constructor
    . case left =>
      simp [Function.Injective]
      intro a b
      sorry
    . case right =>
      sorry
