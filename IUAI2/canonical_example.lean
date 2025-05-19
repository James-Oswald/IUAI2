import Canonical

theorem t1 (a : Nat) : a + 0 = 0 + a :=
  by canonical

theorem t2 (b : Nat) : ∀ (n : Nat), n.add b = b.add n → n.succ.add b = (b.add n).succ :=
  by canonical

theorem t3 (a b : Nat) : a + b = b + a :=
  by canonical [t1, t2]

-- example (a b : Nat) : a + b = b + a :=
--   by canonical 200
