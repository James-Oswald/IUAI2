
import Mathlib.Computability.Language

-- The canonical type of binary strings
abbrev BinStr : Type := List Bool

abbrev BinStringN (n : Nat) : Type := { l : BinStr // l.length = n }
