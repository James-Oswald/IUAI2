
import Mathlib.Data.Seq.Seq

--The type of possibly infinite binary strings

/--
The type of possibly infinite binary strings.

This is modeled as functions from the natural numbers to optional booleans,
that hold under the seq property.
-/
def BinStr : Type := Stream'.Seq Bool
deriving Inhabited

namespace BinStr

/--
Prints a binary string up to limit digits.
-/
def toString (b : BinStr) (limit : Nat := 100) : String :=
  if limit = 0 then
    "..." --If we've reached the limit but the string is not done
  else
    match b.get? 0 with
    | none => "" --If we've reached the end of the sequence
    | some v => (ite v "1" "0") ++ BinStr.toString b.tail (limit - 1)

instance : Repr BinStr where
  reprPrec b _ := BinStr.toString b

/--
A binary string is finite if there is an index at which terminates,
note that this is of course uncomputable
-/
@[simp]
def isFinite (b : BinStr) : Prop := b.Terminates

/--
Reiteration of `Terminates` from `Stream'.Seq`
-/
lemma isFinite_def (b : BinStr) :
b.isFinite ↔ ∃ n, b.get? n = none := by
  simp only [isFinite, Stream'.Seq.Terminates, Stream'.Seq.TerminatedAt]

def len (b : BinStr) (H : b.isFinite) : Nat := b.length H

end BinStr
