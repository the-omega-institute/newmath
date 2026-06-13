namespace ConformalCounting

def isFail (b : Bool) : Bool :=
  b

def countFails : List Bool -> Nat
  | [] => 0
  | b :: bs =>
      match b with
      | false => countFails bs
      | true => countFails bs + 1

def cumFail (cal : List Bool) (i : Nat) : Nat :=
  countFails (cal.take (i + 1))

def consvOK (cal : List Bool) (alphaNum alphaDen i : Nat) : Prop :=
  (1 + cumFail cal i) * alphaDen <= alphaNum * (1 + (i + 1))

def leBool : Nat -> Nat -> Bool
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => leBool a b

theorem leBool_true_le (a b : Nat) :
    leBool a b = true -> a <= b := by
  induction a generalizing b with
  | zero =>
      intro _
      exact Nat.zero_le b
  | succ a ih =>
      cases b with
      | zero =>
          intro h
          change false = true at h
          cases h
      | succ b =>
          intro h
          change leBool a b = true at h
          exact Nat.succ_le_succ (ih b h)

def consvOKBool (cal : List Bool) (alphaNum alphaDen i : Nat) : Bool :=
  leBool ((1 + cumFail cal i) * alphaDen) (alphaNum * (1 + (i + 1)))

def selectIdxFrom (cal : List Bool) (alphaNum alphaDen : Nat) : Nat -> Option Nat
  | 0 => none
  | n + 1 =>
      let i := n
      if consvOKBool cal alphaNum alphaDen i then
        some i
      else
        selectIdxFrom cal alphaNum alphaDen n

def selectIdx (cal : List Bool) (alphaNum alphaDen : Nat) : Option Nat :=
  selectIdxFrom cal alphaNum alphaDen cal.length

def okCount (_cal : List Bool) (sel : Option Nat) : Nat :=
  match sel with
  | none => 0
  | some i => i + 1

def evalFailOK (cal : List Bool) (sel : Option Nat) : Nat :=
  match sel with
  | none => 0
  | some i => cumFail cal i

theorem length_take_of_le
    {alpha : Type} (xs : List alpha) (n : Nat) :
    n <= xs.length -> (xs.take n).length = n := by
  induction xs generalizing n with
  | nil =>
      cases n with
      | zero =>
          intro _
          rfl
      | succ n =>
          intro h
          cases h
  | cons x xs ih =>
      cases n with
      | zero =>
          intro _
          rfl
      | succ n =>
          intro h
          change (x :: xs.take n).length = n + 1
          change (xs.take n).length + 1 = n + 1
          rw [ih n (Nat.le_of_succ_le_succ h)]

theorem countFails_take_le (xs : List Bool) (m n : Nat) :
    m <= n -> countFails (xs.take m) <= countFails (xs.take n) := by
  intro hmn
  induction xs generalizing m n with
  | nil =>
      cases m with
      | zero =>
          exact Nat.zero_le (countFails (List.take n ([] : List Bool)))
      | succ m =>
          cases n with
          | zero =>
              cases hmn
          | succ n =>
              change 0 <= 0
              exact Nat.zero_le 0
  | cons x xs ih =>
      cases m with
      | zero =>
          exact Nat.zero_le (countFails ((x :: xs).take n))
      | succ m =>
          cases n with
          | zero =>
              cases hmn
          | succ n =>
              change countFails (x :: xs.take m) <= countFails (x :: xs.take n)
              cases x with
              | false =>
                  change countFails (xs.take m) <= countFails (xs.take n)
                  exact ih m n (Nat.le_of_succ_le_succ hmn)
              | true =>
                  change countFails (xs.take m) + 1 <= countFails (xs.take n) + 1
                  exact Nat.succ_le_succ (ih m n (Nat.le_of_succ_le_succ hmn))

theorem fail_closed_selects_empty
    (cal : List Bool) (alphaNum alphaDen : Nat) :
    selectIdx cal alphaNum alphaDen = none ->
      okCount cal (selectIdx cal alphaNum alphaDen) = 0 := by
  intro h
  rw [h]
  rfl

theorem selectIdxFrom_satisfies
    (cal : List Bool) (alphaNum alphaDen fuel i : Nat) :
    selectIdxFrom cal alphaNum alphaDen fuel = some i ->
      consvOK cal alphaNum alphaDen i := by
  induction fuel with
  | zero =>
      intro h
      change none = some i at h
      cases h
  | succ n ih =>
      intro h
      change (if consvOKBool cal alphaNum alphaDen n then some n
        else selectIdxFrom cal alphaNum alphaDen n) = some i at h
      cases hc : consvOKBool cal alphaNum alphaDen n with
      | false =>
        rw [hc] at h
        exact ih h
      | true =>
        rw [hc] at h
        cases h
        unfold consvOK
        unfold consvOKBool at hc
        exact leBool_true_le _ _ hc

theorem selected_satisfies_conservative_bound
    (cal : List Bool) (alphaNum alphaDen i : Nat) :
    selectIdx cal alphaNum alphaDen = some i ->
      (1 + cumFail cal i) * alphaDen <= alphaNum * (1 + (i + 1)) := by
  intro h
  exact selectIdxFrom_satisfies cal alphaNum alphaDen cal.length i h

theorem selectIdxFrom_lt
    (cal : List Bool) (alphaNum alphaDen fuel i : Nat) :
    selectIdxFrom cal alphaNum alphaDen fuel = some i -> i < fuel := by
  induction fuel with
  | zero =>
      intro h
      change none = some i at h
      cases h
  | succ n ih =>
      intro h
      change (if consvOKBool cal alphaNum alphaDen n then some n
        else selectIdxFrom cal alphaNum alphaDen n) = some i at h
      cases hc : consvOKBool cal alphaNum alphaDen n with
      | false =>
          rw [hc] at h
          exact Nat.lt_succ_of_lt (ih h)
      | true =>
          rw [hc] at h
          cases h
          exact Nat.lt_succ_self _

theorem selectIdx_lt
    (cal : List Bool) (alphaNum alphaDen i : Nat) :
    selectIdx cal alphaNum alphaDen = some i -> i < cal.length := by
  intro h
  exact selectIdxFrom_lt cal alphaNum alphaDen cal.length i h

theorem coverage_counting_correct
    (cal : List Bool) (alphaNum alphaDen i : Nat) :
    selectIdx cal alphaNum alphaDen = some i ->
      okCount cal (selectIdx cal alphaNum alphaDen) = (cal.take (i + 1)).length := by
  intro h
  rw [h]
  show i + 1 = (cal.take (i + 1)).length
  have hlt : i < cal.length := selectIdx_lt cal alphaNum alphaDen i h
  rw [length_take_of_le cal (i + 1) (Nat.succ_le_of_lt hlt)]

theorem cumFail_monotone
    (cal : List Bool) (i j : Nat) :
    i <= j -> cumFail cal i <= cumFail cal j := by
  intro hij
  unfold cumFail
  exact countFails_take_le cal (i + 1) (j + 1) (Nat.succ_le_succ hij)

#print axioms fail_closed_selects_empty
#print axioms selected_satisfies_conservative_bound
#print axioms coverage_counting_correct
#print axioms cumFail_monotone

end ConformalCounting
