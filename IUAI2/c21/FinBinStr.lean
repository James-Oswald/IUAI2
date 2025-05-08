
import Mathlib.Tactic.Lemma
import Mathlib.Data.Seq.Seq
import IUAI2.c21.BinStr

/--
A finite binary string is seen as a list of booleans
-/
def FinBinStr : Type := List Bool
deriving Inhabited, DecidableEq

namespace FinBinStr

def toString : FinBinStr -> String
| [] => ""
| b => List.toString b

instance : Repr FinBinStr where
  reprPrec b _ := FinBinStr.toString b

end FinBinStr
