
import Lean
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
open Lean


open Lean Elab Term

syntax (name := binStrLit) "b#" noWs num : term

@[term_elab binStrLit]
def elabBinStr : TermElab := fun stx expectedType? => do
  let numStx := stx[1]
  let s := (numStx.isLit? `num).getD ""
  -- Build a list of Bool terms from the digit characters
  let boolTerms ← s.toList.mapM fun c =>
    match c with
    | '0' => `(false)
    | '1' => `(true)
    | _   => throwErrorAt numStx "invalid binary digit: {c}"
  let boolArr := boolTerms.toArray
  let listTerm ← `([ $[$boolArr],* ])
  elabTerm listTerm expectedType?

open Lean PrettyPrinter Delaborator SubExpr

@[delab app.List.cons, delab app.List.nil]
def delabBinStr : Delab := do
  let e ← getExpr
  let some digits ← extractBinStr e | failure
  let numStx := Syntax.mkNumLit digits
  `(b#$numStx)
  where
    extractBinStr : Expr → DelabM (Option String) := fun e =>
      match e with
      | .app (.app (.app (.const ``List.cons _) (.const ``Bool _)) val) rest => do
          let bit ← match val with
            | .const ``Bool.true _  => pure '1'
            | .const ``Bool.false _ => pure '0'
            | _ => return none
          let some restDigits ← extractBinStr rest | return none
          return some (String.ofList (bit :: restDigits.toList))
      | .app (.const ``List.nil _) (.const ``Bool _) =>
          return some ""
      | _ => return none

#eval b#1101
