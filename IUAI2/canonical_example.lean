import Canonical

theorem t1 (a : Nat) : a + 0 = 0 + a :=
  by canonical

theorem t2 (b : Nat) : ∀ (n : Nat), n.add b = b.add n → n.succ.add b = (b.add n).succ :=
  by canonical

theorem t3 (a b : Nat) : a + b = b + a :=
  by canonical [t1, t2]

structure BigNumber where
  data : Nat
  property : data > 2000000

example : BigNumber := by
  canonical

def two := 2

-- Canonical produces an invalid proof (when clicking quick fix)??:
def le_thing : ∀ a b : Nat, a ≤ b → a < b ∨ a = b := by canonical 10
-- This now uses `sorry`...
example : ∀ a : Nat, a ≤ 1 → a = 0 ∨ a = 1 := by canonical [le_thing]
