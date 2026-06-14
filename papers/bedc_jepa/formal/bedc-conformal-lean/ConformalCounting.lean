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

def countLE (t : Nat) : List Nat -> Nat
  | [] => 0
  | x :: xs =>
      match leBool x t with
      | false => countLE t xs
      | true => countLE t xs + 1

def AllLE (x : Nat) : List Nat -> Prop
  | [] => True
  | y :: ys => x <= y ∧ AllLE x ys

def Sorted : List Nat -> Prop
  | [] => True
  | x :: xs => AllLE x xs ∧ Sorted xs

def kthSmallest : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | x :: _, 1 => x
  | _ :: xs, k + 2 => kthSmallest xs (k + 1)

private theorem le_leBool_true (a b : Nat) :
    a <= b -> leBool a b = true := by
  induction a generalizing b with
  | zero =>
      intro _
      rfl
  | succ a ih =>
      cases b with
      | zero =>
          intro h
          cases h
      | succ b =>
          intro h
          change leBool a b = true
          exact ih b (Nat.le_of_succ_le_succ h)

private theorem countLE_cons_of_le (t x : Nat) (xs : List Nat) :
    x <= t -> countLE t (x :: xs) = countLE t xs + 1 := by
  intro h
  change (match leBool x t with
    | false => countLE t xs
    | true => countLE t xs + 1) = countLE t xs + 1
  rw [le_leBool_true x t h]

private theorem allLE_kthSmallest
    (x : Nat) (xs : List Nat) (k : Nat) :
    AllLE x xs -> k <= xs.length -> 1 <= k ->
      x <= kthSmallest xs k := by
  induction xs generalizing k with
  | nil =>
      intro _ hlen hpos
      cases k with
      | zero =>
          cases hpos
      | succ k =>
          cases hlen
  | cons y ys ih =>
      intro hAll hlen hpos
      change x <= y ∧ AllLE x ys at hAll
      cases hAll with
      | intro hxy htail =>
          cases k with
          | zero =>
              cases hpos
          | succ k =>
              cases k with
              | zero =>
                  exact hxy
              | succ k =>
                  change x <= kthSmallest ys (k + 1)
                  have htailLen : k + 1 <= ys.length :=
                    Nat.le_of_succ_le_succ hlen
                  have htailPos : 1 <= k + 1 :=
                    Nat.succ_le_succ (Nat.zero_le k)
                  exact ih (k + 1) htail htailLen htailPos

theorem coverage_count_ge_k
    (scores : List Nat) (k : Nat) :
    Sorted scores -> k <= scores.length ->
      k <= countLE (kthSmallest scores k) scores := by
  induction scores generalizing k with
  | nil =>
      intro _ hlen
      cases k with
      | zero =>
          exact Nat.zero_le 0
      | succ k =>
          cases hlen
  | cons x xs ih =>
      intro hSorted hlen
      change AllLE x xs ∧ Sorted xs at hSorted
      cases hSorted with
      | intro hAll hTailSorted =>
          cases k with
          | zero =>
              exact Nat.zero_le (countLE (kthSmallest (x :: xs) 0) (x :: xs))
          | succ k =>
              have htailLen : k <= xs.length :=
                Nat.le_of_succ_le_succ hlen
              cases k with
              | zero =>
                  change 1 <= countLE x (x :: xs)
                  rw [countLE_cons_of_le x x xs (Nat.le_refl x)]
                  exact Nat.succ_le_succ (Nat.zero_le (countLE x xs))
              | succ k =>
                  change k + 2 <=
                    countLE (kthSmallest xs (k + 1)) (x :: xs)
                  have htailLen' : k + 1 <= xs.length := htailLen
                  have htailCount :
                      k + 1 <= countLE (kthSmallest xs (k + 1)) xs :=
                    ih (k + 1) hTailSorted htailLen'
                  have hxThreshold :
                      x <= kthSmallest xs (k + 1) :=
                    allLE_kthSmallest x xs (k + 1) hAll htailLen'
                      (Nat.succ_le_succ (Nat.zero_le k))
                  rw [countLE_cons_of_le (kthSmallest xs (k + 1)) x xs hxThreshold]
                  exact Nat.succ_le_succ htailCount

private theorem sub_succ_le_sub
    (n m : Nat) :
    n - (m + 1) <= n - m := by
  rw [Nat.sub_succ]
  exact Nat.pred_le (n - m)

private theorem sub_le_sub_left_pure
    {a b : Nat} (h : a <= b) (n : Nat) :
    n - b <= n - a := by
  induction h with
  | refl =>
      exact Nat.le.refl
  | step h ih =>
      exact Nat.le_trans (sub_succ_le_sub n _) ih

theorem finite_coverage_count
    (scores : List Nat) (k : Nat) :
    Sorted scores -> k <= scores.length ->
      scores.length - countLE (kthSmallest scores k) scores <=
        scores.length - k := by
  intro hSorted hlen
  have hcov : k <= countLE (kthSmallest scores k) scores :=
    coverage_count_ge_k scores k hSorted hlen
  exact sub_le_sub_left_pure hcov scores.length

private theorem add_le_cancel_right_pure
    (a b c : Nat) :
    a + c <= b + c -> a <= b := by
  induction c with
  | zero =>
      intro h
      exact h
  | succ c ih =>
      intro h
      change a + c + 1 <= b + c + 1 at h
      exact ih (Nat.le_of_succ_le_succ h)

private theorem sub_add_cancel_pure
    {k n : Nat} (h : k <= n) :
    n - k + k = n := by
  induction k generalizing n with
  | zero =>
      rfl
  | succ k ih =>
      cases n with
      | zero =>
          cases h
      | succ n =>
          rw [Nat.succ_sub_succ_eq_sub]
          change (n - k) + (k + 1) = n + 1
          change ((n - k) + k) + 1 = n + 1
          rw [ih (Nat.le_of_succ_le_succ h)]

private theorem add_sub_of_le_pure
    {a b : Nat} (h : a <= b) :
    a + (b - a) = b := by
  rw [Nat.add_comm a (b - a)]
  exact sub_add_cancel_pure h

private theorem right_distrib_pure
    (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  calc
    (a + b) * c = c * (a + b) := by
      rw [Nat.mul_comm (a + b) c]
    _ = c * a + c * b := by
      rw [Nat.left_distrib]
    _ = a * c + b * c := by
      rw [Nat.mul_comm c a, Nat.mul_comm c b]

private theorem miscoverage_alpha_from_rank
    (n k alphaNum alphaDen : Nat) :
    k <= n ->
    alphaNum <= alphaDen ->
    (alphaDen - alphaNum) * n <= k * alphaDen ->
      (n - k) * alphaDen <= alphaNum * n := by
  intro hkn hAlpha hBudget
  have hBudget' : n * (alphaDen - alphaNum) <= k * alphaDen := by
    rw [Nat.mul_comm n (alphaDen - alphaNum)]
    exact hBudget
  have hDenSplit : alphaNum + (alphaDen - alphaNum) = alphaDen :=
    add_sub_of_le_pure hAlpha
  have hProdSplit :
      n * alphaDen =
        n * alphaNum + n * (alphaDen - alphaNum) := by
    calc
      n * alphaDen =
          n * (alphaNum + (alphaDen - alphaNum)) := by
        rw [hDenSplit]
      _ = n * alphaNum + n * (alphaDen - alphaNum) := by
        rw [Nat.left_distrib]
  have hTotalLe : n * alphaDen <= n * alphaNum + k * alphaDen := by
    rw [hProdSplit]
    exact Nat.add_le_add_left hBudget' (n * alphaNum)
  have hRankSplit : (n - k) * alphaDen + k * alphaDen = n * alphaDen := by
    rw [← right_distrib_pure (n - k) k alphaDen]
    rw [sub_add_cancel_pure hkn]
  have hWithRank :
      (n - k) * alphaDen + k * alphaDen <=
        n * alphaNum + k * alphaDen := by
    rw [hRankSplit]
    exact hTotalLe
  have hCancel :
      (n - k) * alphaDen <= n * alphaNum :=
    add_le_cancel_right_pure ((n - k) * alphaDen) (n * alphaNum)
      (k * alphaDen) hWithRank
  rw [Nat.mul_comm n alphaNum] at hCancel
  exact hCancel

theorem finite_miscoverage_bound
    (scores : List Nat) (k alphaNum alphaDen : Nat) :
    Sorted scores ->
    k <= scores.length ->
    alphaNum <= alphaDen ->
    (alphaDen - alphaNum) * scores.length <= k * alphaDen ->
      (scores.length - countLE (kthSmallest scores k) scores) *
          alphaDen <=
        alphaNum * scores.length := by
  intro hSorted hlen hAlpha hBudget
  have hCov :
      k <= countLE (kthSmallest scores k) scores :=
    coverage_count_ge_k scores k hSorted hlen
  have hMisLe :
      scores.length - countLE (kthSmallest scores k) scores <=
        scores.length - k :=
    sub_le_sub_left_pure hCov scores.length
  have hMisMul :
      (scores.length - countLE (kthSmallest scores k) scores) *
          alphaDen <=
        (scores.length - k) * alphaDen :=
    Nat.mul_le_mul_right alphaDen hMisLe
  have hRankAlpha :
      (scores.length - k) * alphaDen <= alphaNum * scores.length :=
    miscoverage_alpha_from_rank scores.length k alphaNum alphaDen hlen
      hAlpha hBudget
  exact Nat.le_trans hMisMul hRankAlpha

#print axioms fail_closed_selects_empty
#print axioms selected_satisfies_conservative_bound
#print axioms coverage_counting_correct
#print axioms cumFail_monotone
#print axioms coverage_count_ge_k
#print axioms finite_coverage_count
#print axioms finite_miscoverage_bound

end ConformalCounting
