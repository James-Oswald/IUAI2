
import Mathlib
import IUAI2.c21.BinStr

-- Hutter Textbook TM
class TM (_ : Type) where
  Q : Type
  Q_fin : Fintype Q
  Γ : Type
  Γ_fin : Fintype Γ
  A : Set Γ --Alphabet
  δ : Q × Γ -> Option (Q × Γ × Fin 2)
  -- q0 ∈ Q is the start state that the Turing machine is initialized in on the first time step.
  q0 : Q
  B : Γ
  B_not_in_A : B ∉ A
  -- The set of final / accepting states
  F : Set Q

-- The type of tapes for a TM
abbrev TM.Tape (α : Type) [TM α] : Type := Stream' (TM.Γ α)

-- def TM.first_blank (α : Type) [TM α] : Nat :=

-- def TM.string (α : Type) [TM α] TM α

-- The full state of a TM at a single timestep
structure TM.Config (α : Type) [TM α] where
  state: TM.Q α
  tape: TM.Tape α
  head : Nat

--Single step the TM
def TM.step {α : Type} [TM α] (C: TM.Config α): Option (TM.Config α) :=
  -- Read the symbol at the head
  let symbol : TM.Γ α := C.tape C.head
  let next : Option (TM.Q α × TM.Γ α × Fin 2) := (TM.δ ⟨C.state, symbol⟩)
  if H : next.isSome then
    let ⟨nState, nSymb, dir⟩ := next.get H
    let nTape := (C.tape.take C.head) ++ₛ ((C.tape.drop C.head).cons nSymb)
    let nHead := match dir with | 0 => C.head.pred | 1 => C.head.succ
    some ⟨nState, nTape, nHead⟩
  else
    none

-- Run the TM until it halts, if ever
noncomputable def TM.run {α : Type} [TM α] (x : TM.Tape α) : TM.Tape α :=
  let init_cfg : TM.Config α := ⟨TM.q0 α, x, 0⟩
  let rec loop (C : TM.Config α) : TM.Config α :=
    let ns := TM.step C
    if ns.isNone





inductive Symb where
| bit : Bool -> Symb
| blank : Symb

structure TMC where
  Q : Type
  Q_fin : Fintype Q
  δ : Q × Symb -> Option (Q × Symb × Fin 2)
  F : Set Q
