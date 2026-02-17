
import Mathlib
import IUAI2.c21.Bijection
import IUAI2.c21.BinStr

variable (x y z : 𝔹*)
variable (a b c : Bool)
variable (n m l : Nat)

-- Setup and Proof of Length-Lexicographicality of Canonical Bijection ----

@[grind, aesop safe]
def l1_succ (x : 𝔹*) : 𝔹* :=
  match x with
  | [] => [false]
  | false :: x' => true :: x'
  | true :: x' => false :: l1_succ x'

@[grind =, simp, aesop safe]
lemma l1_to_nat_preserves_succ : l1_to_nat (l1_succ x) = (l1_to_nat x).succ := by
  induction x with
  | nil => simp [l1_to_nat, l1_succ]
  | cons a x' =>
    rw [l1_succ.eq_def]
    rw [l1_to_nat.eq_def]
    grind

@[grind, aesop safe]
def same_length_lex : 𝔹* → 𝔹* → Bool
-- Lexicographical order for binary strings of the same length.
| [], [] => false
| a :: xs, b :: ys =>
    if a != b then !a && b
    else same_length_lex xs ys
| _, _ => false

@[simp, grind, aesop safe]
def llex (x y : 𝔹*) : Bool :=
  -- Length-lexicographical order.
  x.length < y.length || (x.length == y.length && same_length_lex x y)

@[simp, grind, aesop safe]
def bool_compareTo : Bool → Bool → SignType
| false, true => -1
| false, false => 0
| true, true => 0
| true, false => 1

@[grind, aesop unsafe]
def length_colex_compareTo : 𝔹* → 𝔹* → SignType
-- Returns -1, 0, or 1 if the first argument is respectively less than, equal to, or greater than
  -- the second argument in length-colexicographical order (i.e. where comparison begins from the
  -- right side of the string).
| [], [] => 0
| [], _ => -1
| _, [] => 1
| a :: x', b :: y' =>
  let tail_result := length_colex_compareTo x' y'
  if tail_result ≠ 0 then tail_result else bool_compareTo a b

@[simp, grind, aesop safe]
def lcolex (x y : 𝔹*) : Bool :=
  -- "Less than" in length-colexicographical order (i.e. where comparison begins from the right
    -- side of the string).
  -- This is convenient because a direct, cons-based definition of colexicographical order can be
    -- given that matches on the same side of the string that `l1_succ` matches on (the left),
    -- simplifying proofs significantly.
  length_colex_compareTo x y == -1


@[grind =, aesop unsafe]
lemma lcolex_compareTo_diff_length :
    x.length ≠ y.length →
    length_colex_compareTo x y = if x.length < y.length then -1 else 1 := by
  intro h
  induction x generalizing y with
  | nil =>
    cases y with
    | nil =>
      simp at h
    | cons b ys =>
      simp [length_colex_compareTo]
  | cons a xs ih =>
    cases y with
    | nil =>
      simp [length_colex_compareTo]
    | cons b ys =>
      have h' : xs.length ≠ ys.length := by simp at h; omega
      have ih_applied := ih ys h'
      rw [length_colex_compareTo]
      simp [ih_applied]
      grind [SignType.neg_eq_zero_iff]

@[grind =, aesop unsafe]
lemma llex_colex_reverse_diff_length :
    x.length ≠ y.length → llex x y = lcolex x.reverse y.reverse := by
  intro h
  rw [llex]
  have h_eq_false : (x.length == y.length) = false := by simp [h]
  simp [h_eq_false]
  suffices (x.length < y.length) = (length_colex_compareTo x.reverse y.reverse == -1) by grind
  have h_rev : x.reverse.length ≠ y.reverse.length := by simp [h]
  rw [lcolex_compareTo_diff_length _ _ h_rev]
  simp_all

@[grind =, aesop unsafe]
lemma lcolex_compareTo_append_same_length :
    x.length = y.length →
    length_colex_compareTo (x ++ [a]) (y ++ [b]) =
    let last_result := bool_compareTo a b
    if last_result ≠ 0 then last_result else length_colex_compareTo x y := by

  intro h
  induction x generalizing y with
  | nil =>
    cases y with
    | nil =>
      simp [length_colex_compareTo]
    | cons c zs =>
      simp at h
  | cons c zs ih =>
    cases y with
    | nil =>
      simp at h
    | cons d ws =>
      simp at h
      simp [length_colex_compareTo]
      have ih_applied := ih ws h
      rw [ih_applied]
      simp
      split
      · rfl
      · rfl
      grind
      grind

@[grind =, aesop unsafe]
lemma llex_colex_reverse_same_length :
    x.length = y.length → llex x y = lcolex x.reverse y.reverse := by
  intro h
  rw [llex, lcolex]
  have h_eq_true : (x.length == y.length) = true := by simp [h]
  have h_lt_false : (x.length < y.length) = false := by grind
  simp [h_eq_true, h_lt_false]
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b ys => simp at h
  | cons a xs ih =>
    cases y with
    | nil => simp at h
    | cons b ys =>
      simp at h
      have h_xs_eq : (xs.length == ys.length) = true := by simp [h]
      have h_xs_lt : (xs.length < ys.length) = false := by grind
      have ih_applied := ih ys h h_xs_eq h_xs_lt
      simp [same_length_lex]
      have h_rev_len : xs.reverse.length = ys.reverse.length := by simp [h]
      rw [lcolex_compareTo_append_same_length _ _]
      simp
      cases a <;> cases b <;> simp [ih_applied]
      grind only

@[grind =, aesop unsafe]
lemma llex_colex_reverse :
llex x y = lcolex x.reverse y.reverse := by
  grind only [= llex_colex_reverse_same_length, = llex_colex_reverse_diff_length]

lemma nat_to_l1_is_length_colexicographical_when_diff_length :
    n ≠ 0 ∧ m ≠ 0 ∧ n < m ∧ (nat_to_l1 n).length ≠ (nat_to_l1 m).length →
    lcolex (nat_to_l1 n) (nat_to_l1 m) := by
  intro ⟨hn_ne_0, hm_ne_0, hn_lt_m, hlen_ne⟩
  rw [lcolex]
  rw [lcolex_compareTo_diff_length _ _ hlen_ne]
  have hn_len : (nat_to_l1 n).length = Nat.log2 n := by
    exact nat_l1_length_formula n hn_ne_0
  have hm_len : (nat_to_l1 m).length = Nat.log2 m := by
    exact nat_l1_length_formula m hm_ne_0
  rw [hn_len, hm_len]
  have hlog_le : Nat.log2 n ≤ Nat.log2 m := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right (Nat.le_of_lt hn_lt_m)
  have hlog_ne : Nat.log2 n ≠ Nat.log2 m := by
    rw [← hn_len, ← hm_len]
    exact hlen_ne
  have hlog_lt : Nat.log2 n < Nat.log2 m := by
    omega
  simp [hlog_lt]

@[simp, grind =, aesop safe]
lemma lcolex_compareTo_refl (x : 𝔹*) :
    length_colex_compareTo x x = 0 := by
  induction x with
  | nil =>
    rfl
  | cons a xs ih =>
    rw [length_colex_compareTo]
    simp [ih]
    cases a <;> rfl

@[grind =, aesop safe]
lemma lcolex_l1_succ (x : 𝔹*) :
    lcolex x (l1_succ x) := by
  induction x with
  | nil =>
    rw [lcolex]
    rw [length_colex_compareTo]
    rfl
    grind
  | cons a xs ih =>
    cases a
    · rw [l1_succ]
      rw [lcolex]
      rw [length_colex_compareTo]
      simp [bool_compareTo]
    · rw [l1_succ]
      rw [lcolex]
      rw [length_colex_compareTo]
      have ih_eq : length_colex_compareTo xs (l1_succ xs) == -1 := by grind
      simp_all

@[grind =, aesop unsafe]
lemma nat_to_l1_llex_nat_to_l1_succ :
    n ≠ 0 → lcolex (nat_to_l1 n) (nat_to_l1 n.succ) := by
  intro hn
  have h_succ : nat_to_l1 n.succ = l1_succ (nat_to_l1 n) := by
    have : l1_to_nat (l1_succ (nat_to_l1 n)) = n.succ := by
      rw [l1_to_nat_preserves_succ]
      rw [nat_to_l1_to_nat n hn]
    have : nat_to_l1 (l1_to_nat (l1_succ (nat_to_l1 n))) = l1_succ (nat_to_l1 n) := by grind
    rw [← this]
    simp [l1_to_nat_preserves_succ, nat_to_l1_to_nat n hn]
  rw [h_succ]
  exact lcolex_l1_succ (nat_to_l1 n)

@[simp, grind =]
lemma lcolex_compareTo_eq_zero_iff :
    length_colex_compareTo x y = 0 ↔ x = y := by
  constructor
  · intro h
    induction x generalizing y with
    | nil =>
      cases y with
      | nil =>
        rfl
      | cons b ys =>
        simp [length_colex_compareTo] at h
    | cons a xs ih =>
      cases y with
      | nil =>
        simp [length_colex_compareTo] at h
      | cons b ys =>
        rw [length_colex_compareTo] at h
        split at h
        · contradiction
        · have xs_eq_ys := ih ys (by grind)
          have a_eq_b : a = b := by
            cases a <;> cases b <;> simp at h <;> rfl
          rw [xs_eq_ys, a_eq_b]
  · intro h
    rw [h]
    exact lcolex_compareTo_refl y

@[grind ., aesop safe]
lemma lcolex_compareTo_trans_neg :
    length_colex_compareTo x y = -1 →
    length_colex_compareTo y z = -1 →
    length_colex_compareTo x z = -1 := by
  intro hab hbc
  induction x generalizing y z with
  | nil =>
    cases z with
    | nil =>
      cases y with
      | nil => simp at hab
      | cons b ys => simp [lcolex_compareTo_diff_length] at hbc
    | cons c zs =>
      rfl
  | cons a xs ih =>
    cases y with
    | nil => simp [lcolex_compareTo_diff_length] at hab
    | cons b ys =>
      cases z with
      | nil => grind
      | cons c zs =>
        rw [length_colex_compareTo] at hab hbc ⊢
        split at hab
        · split at hbc <;> grind
        · split at hbc
          · grind
          · split
            · grind
            · cases a <;> cases b <;> cases c <;> simp at hab hbc ⊢

@[grind ., aesop safe]
lemma lcolex_trans :
    lcolex x y → lcolex y z → lcolex x z := by
  grind

lemma nat_to_l1_is_length_colexicographical_when_same_length :
    n ≠ 0 ∧ n < m ∧ (nat_to_l1 n).length = (nat_to_l1 m).length →
    lcolex (nat_to_l1 n) (nat_to_l1 m) := by
  intro ⟨hn_ne_0, hn_lt_m, hlen_eq⟩

  have : ∀ k, ∀ n m, n ≠ 0 → n < m → (nat_to_l1 n).length = (nat_to_l1 m).length →
         m - n = k → lcolex (nat_to_l1 n) (nat_to_l1 m) := by
    intro k
    induction k with
    | zero => grind
    | succ k' ih =>
      intro n m hn_ne_0 hn_lt_m hlen_eq hk
      by_cases h : m = n.succ
      · rw [h]
        exact nat_to_l1_llex_nat_to_l1_succ n hn_ne_0
      · have hn_succ_lt_m : n.succ < m := by omega
        have hn_succ_ne_0 : n.succ ≠ 0 := by omega
        have hlen_n_succ : (nat_to_l1 n.succ).length = (nat_to_l1 m).length := by
          rw [nat_l1_length_formula n hn_ne_0] at hlen_eq
          rw [nat_l1_length_formula m (by omega)] at hlen_eq
          rw [nat_l1_length_formula n.succ hn_succ_ne_0]
          rw [nat_l1_length_formula m (by omega)]
          have h1 : Nat.log2 n ≤ Nat.log2 n.succ := by
            rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
            exact Nat.log_mono_right (Nat.le_succ n)
          have h2 : Nat.log2 n.succ ≤ Nat.log2 m := by
            rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
            exact Nat.log_mono_right (Nat.le_of_lt hn_succ_lt_m)
          omega
        have h_diff : m - n.succ = k' := by omega
        have ih_applied := ih n.succ m hn_succ_ne_0 hn_succ_lt_m hlen_n_succ h_diff
        have h1 := nat_to_l1_llex_nat_to_l1_succ n hn_ne_0
        exact lcolex_trans (nat_to_l1 n) (nat_to_l1 n.succ) (nat_to_l1 m) h1 ih_applied

  exact this (m - n) n m hn_ne_0 hn_lt_m hlen_eq rfl

@[grind =, aesop safe]
lemma nat_to_l1_is_length_colexicographical :
    n ≠ 0 ∧ n < m → lcolex (nat_to_l1 n) (nat_to_l1 m) := by
  grind [nat_to_l1_is_length_colexicographical_when_same_length,
    nat_to_l1_is_length_colexicographical_when_diff_length]

@[grind =, aesop unsafe]
theorem nat_to_b0_is_length_lexicographical : n < m → llex ⌜n⌝ ⌜m⌝ := by
  -- The canonical bijection from ℕ to 𝔹* orders the binary strings length-lexicographically.
  -- Part of Proposition 2.1.1.
  grind

@[grind ., aesop safe]
theorem lcolex_is_irreflexive : ¬ lcolex x x := by
  intro h1
  induction x with
  | nil => simp_all
  | cons a x' =>
    rw [lcolex] at h1
    rw [length_colex_compareTo.eq_def] at h1
    suffices (
        if length_colex_compareTo x' x' ≠ 0
        then length_colex_compareTo x' x'
        else bool_compareTo a a) = -1 by
      aesop
    have s1 : length_colex_compareTo x' x' ≠ 0 := by aesop
    simp_all

@[grind ., aesop safe]
lemma nat_to_l1_is_length_colexicographical_backwards_contrapositive :
    n ≠ 0 → ¬ n < m → ¬ lcolex (nat_to_l1 n) (nat_to_l1 m) := by
  intro h1 h2 h3
  have s1 : n = m ∨ n > m := by grind
  cases s1
  ·
    have s2 : (nat_to_l1 n) = (nat_to_l1 m) := by grind
    grind
  ·
    have s2 : m < n := by grind
    have s3 : lcolex (nat_to_l1 m) (nat_to_l1 n) = true := by grind
    have s4 : lcolex (nat_to_l1 n) (nat_to_l1 n) = true := by grind
    grind

@[grind ., aesop safe]
lemma nat_to_l1_is_length_colexicographical_backwards :
    n ≠ 0 → lcolex (nat_to_l1 n) (nat_to_l1 m) → n < m := by
  grind only [nat_to_l1_is_length_colexicographical_backwards_contrapositive]

@[grind =]
lemma nat_to_l1_is_length_colexicographical_iff :
n ≠ 0 → (n < m ↔ lcolex (nat_to_l1 n) (nat_to_l1 m)) := by
  grind only [nat_to_l1_is_length_colexicographical_backwards,
    = nat_to_l1_is_length_colexicographical, #b5235b60883b4cfc]

-- A stronger formalization of the claim that the canonical bijection from ℕ to 𝔹* orders the
-- binary strings length-lexicographically.
-- Part of Proposition 2.1.1.
@[grind =]
lemma nat_to_b0_is_length_lexicographical_iff :
    n < m ↔ llex ⌜n⌝ ⌜m⌝ := by
  constructor
  · grind only [= nat_to_b0_is_length_lexicographical]
  · intro h
    have s1 : n + 1 ≠ 0 := by grind
    have s2 := (nat_to_l1_is_length_colexicographical_iff (n + 1) (m + 1) s1).2
    grind only [= llex_colex_reverse, = Nat.to_b0.eq_1, = List.reverse_reverse]


lemma same_length_llex_iff_lex (x y : 𝔹*) (h : x.length = y.length) :
same_length_lex x y = true ↔ List.Lex (· < ·) x y := by
  induction x generalizing y with
  | nil =>
    cases y <;> simp [same_length_lex] at h ⊢
  | cons a xs ih =>
    cases y with
    | nil => grind
    | cons b ys =>
      rw [same_length_lex]
      rw [List.length_cons] at h
      by_cases hxy : a = b
      · simp_all
      · simp only [hxy, ite_true, bne_iff_ne, ne_eq, not_false_eq_true]
        constructor
        · intro h_and
          have : a = false ∧ b = true := by grind
          rw [this.1, this.2]
          exact List.Lex.rel (by decide : false < true)
        · intro h_lex
          cases h_lex with
          | cons h_tail => contradiction
          | rel h_rel =>
            cases a <;> cases b
            · simp at h_rel
            · simp
            · have : ¬(true < false) := by decide
              contradiction
            · simp at h_rel

-- llex is (a computational) equivalent to List.Shortlex.
theorem length_llex_iff_shortlex (x y : 𝔹*) :
llex x y = true ↔ List.Shortlex (· < ·) x y := by
  unfold llex List.Shortlex InvImage
  grind [same_length_llex_iff_lex]

-- Proofs of some additional results for succ and pred on binary strings ----

@[grind, simp, aesop safe]
def b0_succ (x : 𝔹*) :=
  (l1_succ x.reverse).reverse

@[grind =, simp, aesop safe]
lemma b0_to_nat_preserves_succ : ⌜b0_succ x⌝⁻¹ = (⌜x⌝⁻¹) + 1 := by
  grind only [= BinStr.to_nat.eq_1, b0_succ, l1_to_nat_ne_0,
   = List.reverse_reverse, = l1_to_nat_preserves_succ, #0c77, #8f44]

@[grind =, aesop safe]
def l1_pred (x : 𝔹*) :=
  match x with
  | [] => []
  | [false] => []
  | true :: x' => false :: x'
  | false :: x' => true :: l1_pred x'

@[grind, simp, aesop safe]
def b0_pred (x : 𝔹*) :=
  (l1_pred x.reverse).reverse

@[grind =, simp, aesop safe]
lemma l1_pred_l1_succ (x : 𝔹*): l1_pred (l1_succ x) = x := by
  induction x with
  | nil => simp [l1_succ, l1_pred]
  | cons a x' ih =>
    rw [l1_succ.eq_def]
    cases a
    · simp only [l1_pred]
    · grind only [l1_pred, l1_succ]

@[grind =, simp, aesop safe]
lemma b0_pred_b0_succ (x : 𝔹*) : b0_pred (b0_succ x) = x := by
  simp

@[grind =, simp, aesop unsafe]
lemma l1_succ_l1_pred (x : 𝔹*): x ≠ [] → l1_succ (l1_pred x) = x := by
  induction x with
  | nil => simp
  | cons a x' ih =>
    intro h
    match mh: x' with
    | [] =>
      rw [l1_succ.eq_def]
      rw [l1_pred.eq_def]
      grind only [#5790, #16d8]
    | b :: x'' =>
      have ih1 : l1_succ (l1_pred (b :: x'')) = b :: x'' := by simp_all
      rw [l1_pred.eq_def]
      grind only [l1_succ]

@[grind =, simp, aesop unsafe]
lemma b0_succ_b0_pred (x : 𝔹*): x ≠ [] → b0_succ (b0_pred x) = x := by
  grind [l1_pred.eq_def, l1_succ.eq_def]

@[grind =, simp, aesop unsafe]
lemma l1_to_nat_preserves_pred : x ≠ [] → l1_to_nat (l1_pred x) = (l1_to_nat x).pred := by
  intro h
  suffices (l1_to_nat (l1_pred x)).succ = l1_to_nat x by
    have s1 : (l1_to_nat x).pred.succ = l1_to_nat x := by
      rw [Nat.succ_pred (by simp [l1_to_nat_ne_0])]
    symm
    suffices (l1_to_nat (l1_pred x)).succ = (l1_to_nat x).pred.succ by grind
    suffices (l1_to_nat (l1_pred x)).succ = (l1_to_nat x) by simp_all
    rw [← l1_to_nat_preserves_succ]
    rw [l1_succ_l1_pred x (by exact h)]
  symm
  have s1 : l1_to_nat (l1_succ (l1_pred x)) = (l1_to_nat (l1_pred x)).succ := by
    refine l1_to_nat_preserves_succ ?_
  rw [l1_succ_l1_pred x h] at s1
  exact s1

@[grind =, simp, aesop unsafe]
lemma b0_to_nat_preserves_pred : x ≠ [] → ⌜b0_pred x⌝⁻¹ = (⌜x⌝⁻¹) - 1 := by
  simp_all only [ne_eq, BinStr.to_nat, b0_pred, List.reverse_reverse,
    List.reverse_eq_nil_iff, not_false_eq_true, l1_to_nat_preserves_pred,
    Nat.pred_eq_sub_one, implies_true]
