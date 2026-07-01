namespace BEDC.Derived.Window6LiveTailCongruence

/-!
Myhill-Nerode right congruence for the Window6 live-tail scanner: suffix
windows in the real word factor through the five-bit tail, giving a 13-state
exactness witness. This is a STATE anchor, distinct from SeamGluing's
valuation-count decomposition.
-/

def windows6 : List Bool -> List (List Bool)
  | [] => []
  | [_a] => []
  | [_a, _b] => []
  | [_a, _b, _c] => []
  | [_a, _b, _c, _d] => []
  | [_a, _b, _c, _d, _e] => []
  | a :: b :: c :: d :: e :: f :: rest =>
      [a, b, c, d, e, f] :: windows6 (b :: c :: d :: e :: f :: rest)

def tail5 : List Bool -> List Bool
  | [] => []
  | [a] => [a]
  | [a, b] => [a, b]
  | [a, b, c] => [a, b, c]
  | [a, b, c, d] => [a, b, c, d]
  | [a, b, c, d, e] => [a, b, c, d, e]
  | _ :: b :: c :: d :: e :: f :: rest => tail5 (b :: c :: d :: e :: f :: rest)

def realSuffixWindows (p s : List Bool) : List (List Bool) :=
  windows6 (List.drop (p.length - 5) (p ++ s))

theorem five_le_five_cons (a b c d e : Bool) (rest : List Bool) :
    5 ≤ (a :: b :: c :: d :: e :: rest).length := by
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  apply Nat.succ_le_succ
  exact Nat.zero_le rest.length

theorem not_five_le_one : ¬ 5 ≤ 1 := by
  intro h
  exact Nat.not_succ_le_zero 3 (Nat.le_of_succ_le_succ h)

theorem not_five_le_two : ¬ 5 ≤ 2 := by
  intro h
  exact Nat.not_succ_le_zero 2
    (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ h))

theorem not_five_le_three : ¬ 5 ≤ 3 := by
  intro h
  exact Nat.not_succ_le_zero 1
    (Nat.le_of_succ_le_succ
      (Nat.le_of_succ_le_succ
        (Nat.le_of_succ_le_succ h)))

theorem not_five_le_four : ¬ 5 ≤ 4 := by
  intro h
  exact Nat.not_succ_le_zero 0
    (Nat.le_of_succ_le_succ
      (Nat.le_of_succ_le_succ
        (Nat.le_of_succ_le_succ
          (Nat.le_of_succ_le_succ h))))

theorem zero_ne_one : 0 ≠ 1 := by
  intro h
  exact Nat.noConfusion h

theorem one_ne_five : 1 ≠ 5 := by
  intro h
  have h1 : 0 = 4 := Nat.succ.inj h
  exact Nat.noConfusion h1

theorem two_ne_five : 2 ≠ 5 := by
  intro h
  have h1 : 1 = 4 := Nat.succ.inj h
  have h2 : 0 = 3 := Nat.succ.inj h1
  exact Nat.noConfusion h2

theorem three_ne_five : 3 ≠ 5 := by
  intro h
  have h1 : 2 = 4 := Nat.succ.inj h
  have h2 : 1 = 3 := Nat.succ.inj h1
  have h3 : 0 = 2 := Nat.succ.inj h2
  exact Nat.noConfusion h3

theorem four_ne_five : 4 ≠ 5 := by
  intro h
  have h1 : 3 = 4 := Nat.succ.inj h
  have h2 : 2 = 3 := Nat.succ.inj h1
  have h3 : 1 = 2 := Nat.succ.inj h2
  have h4 : 0 = 1 := Nat.succ.inj h3
  exact zero_ne_one h4

theorem six_ne_five : 6 ≠ 5 := by
  intro h
  have h1 : 5 = 4 := Nat.succ.inj h
  exact four_ne_five h1.symm

theorem not_six_cons_length_eq_five
    (a b c d e f : Bool) (rest : List Bool) :
    (a :: b :: c :: d :: e :: f :: rest).length ≠ 5 := by
  intro h
  have h1 : (b :: c :: d :: e :: f :: rest).length = 4 := Nat.succ.inj h
  have h2 : (c :: d :: e :: f :: rest).length = 3 := Nat.succ.inj h1
  have h3 : (d :: e :: f :: rest).length = 2 := Nat.succ.inj h2
  have h4 : (e :: f :: rest).length = 1 := Nat.succ.inj h3
  have h5 : (f :: rest).length = 0 := Nat.succ.inj h4
  exact Nat.noConfusion h5

theorem window6_live_tail_factor : ∀ (p s : List Bool), 5 ≤ p.length ->
    realSuffixWindows p s = windows6 (tail5 p ++ s)
  | [], _s, hp => by
      cases hp
  | [_a], _s, hp => by
      exact False.elim (not_five_le_one hp)
  | [_a, _b], _s, hp => by
      exact False.elim (not_five_le_two hp)
  | [_a, _b, _c], _s, hp => by
      exact False.elim (not_five_le_three hp)
  | [_a, _b, _c, _d], _s, hp => by
      exact False.elim (not_five_le_four hp)
  | [_a, _b, _c, _d, _e], _s, _hp => by
      rfl
  | _a :: b :: c :: d :: e :: f :: rest, s, _hp => by
      exact window6_live_tail_factor (b :: c :: d :: e :: f :: rest) s
        (five_le_five_cons b c d e f rest)

def feedEmit (tail s : List Bool) : List (List Bool) :=
  windows6 (tail ++ s)

theorem windows6_eq_feedEmit (tail s : List Bool) :
    windows6 (tail ++ s) = feedEmit tail s := by
  rfl

theorem window6_live_tail_congruence (p q s : List Bool)
    (hp : 5 ≤ p.length) (hq : 5 ≤ q.length) (hpq : tail5 p = tail5 q) :
    realSuffixWindows p s = realSuffixWindows q s := by
  exact Eq.trans
    (window6_live_tail_factor p s hp)
    (Eq.trans (congrArg (fun t => windows6 (t ++ s)) hpq)
      (window6_live_tail_factor q s hq).symm)

def noAdj : Bool -> List Bool -> Bool
  | _, [] => true
  | prev, a :: rest => (!(prev && a)) && noAdj a rest

def T5 : List (List Bool) :=
  [ [false, false, false, false, false],
    [false, false, false, false, true],
    [false, false, false, true, false],
    [false, false, true, false, false],
    [false, false, true, false, true],
    [false, true, false, false, false],
    [false, true, false, false, true],
    [false, true, false, true, false],
    [true, false, false, false, false],
    [true, false, false, false, true],
    [true, false, false, true, false],
    [true, false, true, false, false],
    [true, false, true, false, true] ]

theorem T5_length : T5.length = 13 := rfl

theorem T5_noAdj_00000 : noAdj false [false, false, false, false, false] = true := rfl
theorem T5_noAdj_00001 : noAdj false [false, false, false, false, true] = true := rfl
theorem T5_noAdj_00010 : noAdj false [false, false, false, true, false] = true := rfl
theorem T5_noAdj_00100 : noAdj false [false, false, true, false, false] = true := rfl
theorem T5_noAdj_00101 : noAdj false [false, false, true, false, true] = true := rfl
theorem T5_noAdj_01000 : noAdj false [false, true, false, false, false] = true := rfl
theorem T5_noAdj_01001 : noAdj false [false, true, false, false, true] = true := rfl
theorem T5_noAdj_01010 : noAdj false [false, true, false, true, false] = true := rfl
theorem T5_noAdj_10000 : noAdj false [true, false, false, false, false] = true := rfl
theorem T5_noAdj_10001 : noAdj false [true, false, false, false, true] = true := rfl
theorem T5_noAdj_10010 : noAdj false [true, false, false, true, false] = true := rfl
theorem T5_noAdj_10100 : noAdj false [true, false, true, false, false] = true := rfl
theorem T5_noAdj_10101 : noAdj false [true, false, true, false, true] = true := rfl

theorem window6_append_false_single :
    ∀ (a : List Bool), a.length = 5 -> windows6 (a ++ [false]) = [a ++ [false]]
  | [], h => by
      cases h
  | [_a], h => by
      exact False.elim (one_ne_five h)
  | [_a, _b], h => by
      exact False.elim (two_ne_five h)
  | [_a, _b, _c], h => by
      exact False.elim (three_ne_five h)
  | [_a, _b, _c, _d], h => by
      exact False.elim (four_ne_five h)
  | [_a, _b, _c, _d, _e], _h => by
      rfl
  | a :: b :: c :: d :: e :: f :: rest, h => by
      exact False.elim (not_six_cons_length_eq_five a b c d e f rest h)

theorem length_five_window6_append_false_injective :
    ∀ (a b : List Bool), a.length = 5 -> b.length = 5 ->
      windows6 (a ++ [false]) = windows6 (b ++ [false]) -> a = b
  | [], _b, ha, _hb, _h => by
      cases ha
  | [_a], _b, ha, _hb, _h => by
      exact False.elim (one_ne_five ha)
  | [_a, _b], _b2, ha, _hb, _h => by
      exact False.elim (two_ne_five ha)
  | [_a, _b, _c], _b2, ha, _hb, _h => by
      exact False.elim (three_ne_five ha)
  | [_a, _b, _c, _d], _b2, ha, _hb, _h => by
      exact False.elim (four_ne_five ha)
  | [_a0, _a1, _a2, _a3, _a4], [], _ha, hb, _h => by
      cases hb
  | [_a0, _a1, _a2, _a3, _a4], [_b0], _ha, hb, _h => by
      exact False.elim (one_ne_five hb)
  | [_a0, _a1, _a2, _a3, _a4], [_b0, _b1], _ha, hb, _h => by
      exact False.elim (two_ne_five hb)
  | [_a0, _a1, _a2, _a3, _a4], [_b0, _b1, _b2], _ha, hb, _h => by
      exact False.elim (three_ne_five hb)
  | [_a0, _a1, _a2, _a3, _a4], [_b0, _b1, _b2, _b3], _ha, hb, _h => by
      exact False.elim (four_ne_five hb)
  | [a0, a1, a2, a3, a4], [b0, b1, b2, b3, b4], _ha, _hb, h => by
      cases h
      rfl
  | [_a0, _a1, _a2, _a3, _a4], b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: brest,
      _ha, hb, _h => by
      exact False.elim (not_six_cons_length_eq_five b0 b1 b2 b3 b4 b5 brest hb)
  | a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: arest, _b, ha, _hb, _h => by
      exact False.elim (not_six_cons_length_eq_five a0 a1 a2 a3 a4 a5 arest ha)

theorem window6_live_tail_minimality_length_five (a b : List Bool)
    (ha : a.length = 5) (hb : b.length = 5) (hne : a ≠ b) :
    windows6 (a ++ [false]) ≠ windows6 (b ++ [false]) := by
  intro h
  exact hne (length_five_window6_append_false_injective a b ha hb h)

theorem realSuffixWindows_six_false_empty :
    realSuffixWindows [false, false, false, false, false, false] [] = [] := by
  rfl

theorem realSuffixWindows_six_false_one_suffix :
    realSuffixWindows [false, false, false, false, false, false] [false] =
      [[false, false, false, false, false, false]] := by
  rfl

theorem window6_live_tail_factor_concrete :
    realSuffixWindows [true, false, true, false, true, false] [true] =
      windows6 (tail5 [true, false, true, false, true, false] ++ [true]) := by
  exact window6_live_tail_factor
    [true, false, true, false, true, false]
    [true]
    (five_le_five_cons true false true false true [false])

theorem windows6_10101_false :
    windows6 ([true, false, true, false, true] ++ [false]) =
      [[true, false, true, false, true, false]] := by
  rfl

end BEDC.Derived.Window6LiveTailCongruence
