
import Mathlib.Data.Stream.Defs

-- The canonical type of binary strings
abbrev BinStr : Type := List Bool

notation "𝔹*" => BinStr

def BinStr.toString (s : BinStr) : String :=
  s.foldl (fun acc b => acc ++ if b then "1" else "0") ""

instance : ToString BinStr where
  toString := BinStr.toString

-- Length of a binary string
prefix:max "ℓ" => List.length

/--
The type of Binary strings of a fixed length n.
-/
abbrev BinStringN (n : Nat) : Type := { l : 𝔹* // l.length = n }

prefix:max "𝔹^" => BinStringN

/--
The type of infinite binary strings.
-/
abbrev BinStream : Type := Stream' Bool

notation "𝔹∞" => BinStream
