
import IUAI2.c21.BinStr
import IUAI2.c21.FinBinStr

namespace FinBinStr
/--
A finite binary string when viewed as a possibly infinite binary string
is finite.
-/
lemma toBinStr_isFinite (b : FinBinStr) : b.toBinStr.isFinite := by
  simp only [BinStr.isFinite, Stream'.Seq.Terminates,
    Stream'.Seq.TerminatedAt, toBinStr,
    Stream'.Seq.ofList_get?, getElem?_eq_none_iff, not_lt]
  exists b.length

/--
Version of `asSeq` that bundles the condition that the
possibly infinite binary string is finite
-/
def toBinStr' (b : FinBinStr) : {b : BinStr // b.isFinite} :=
  ⟨b.toBinStr, b.toBinStr_isFinite⟩

-- Coercions of from `FinBinStr` to `BinStr` and vice versa
namespace BinStr

def asFinBinStr (a : BinStr) (H: a.isFinite) : FinBinStr :=
  a.toList H

def asFinBinStr' (a : {b : BinStr // b.isFinite}) : FinBinStr :=
  a.val.toList a.property

end BinStr

def toBinStr (b : FinBinStr) : BinStr :=
  Stream'.Seq.ofList b

instance : Coe FinBinStr BinStr where
  coe := toBinStr

end FinBinStr

lemma asFinBinStr_asFinBinStr'_left_inv :
Function.LeftInverse FinBinStr.asSeq' BinStr.asFinBinStr' := by
  simp only [Function.LeftInverse, BinStr.isFinite, Subtype.forall]
  intro b bH
  simp only [FinBinStr.asSeq', BinStr.isFinite, BinStr.asFinBinStr', Subtype.mk.injEq]
  simp only [FinBinStr.asSeq, Stream'.Seq.ofList_toList]

lemma asFinBinStr_asFinBinStr'_right_inv :
Function.RightInverse FinBinStr.asSeq' BinStr.asFinBinStr' := by
  simp only [Function.RightInverse, Function.LeftInverse, BinStr.isFinite, Subtype.forall]
  intro b
  simp only [BinStr.asFinBinStr', BinStr.isFinite, FinBinStr.asSeq']
  simp only [FinBinStr.asSeq, Stream'.Seq.toList_ofList]

def FinBinStr_equiv: {b : BinStr // b.isFinite} ≃ FinBinStr :=
  Equiv.mk BinStr.asFinBinStr' FinBinStr.asSeq'
    (asFinBinStr_asFinBinStr'_left_inv) (asFinBinStr_asFinBinStr'_right_inv)
