
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

def l (n : Nat) : Nat :=
    (Nat.log2 (n + 1)) + 1

def B (n : Nat) (i : Nat) :=
     n ⌊/⌋ 2^((l n) - i) % 2

def B' (n : Nat) : BinString :=
    { u := List.range ((l n)) |>.tail |>.map (fun i => B n i) }

def ce (n : Nat) : BinString :=
    B' (n + 1) |>.u.tail |> BinString.mk

theorem canonicalBijection : Function.Bijective ce := by
    constructor
    sorry
