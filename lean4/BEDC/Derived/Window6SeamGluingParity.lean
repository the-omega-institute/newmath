namespace BEDC.Derived.Window6SeamGluingParity

set_option maxRecDepth 4096

/-!
Window6 even-two-hit seam gluing is a composition/gluing-law deliverable:
the scanner count across an append splits into left, right, and five seam windows.
This file is not a recurrence, trace, congruence, or flattening-bijection anchor.
-/

def noAdj : List Bool → Bool
  | [] => true
  | x :: xs =>
      match xs with
      | [] => true
      | y :: ys => (!(x && y)) && noAdj (y :: ys)

def bitHit : Bool → Nat
  | false => 0
  | true => 1

def eqTwo : Nat → Bool
  | 0 => false
  | 1 => false
  | 2 => true
  | _ + 3 => false

def inW2 (w : List Bool) : Bool :=
  match w with
  | [] => false
  | a :: wa =>
      match wa with
      | [] => false
      | b :: wb =>
          match wb with
          | [] => false
          | c :: wc =>
              match wc with
              | [] => false
              | d :: wd =>
                  match wd with
                  | [] => false
                  | e :: we =>
                      match we with
                      | [] => false
                      | f :: rest =>
                          match rest with
                          | [] =>
                              noAdj [a, b, c, d, e, f] &&
                                eqTwo (bitHit a + bitHit b + bitHit c + bitHit d + bitHit e + bitHit f)
                          | _ :: _ => false

def hit6 (a b c d e f : Bool) : Nat :=
  bitHit (inW2 [a, b, c, d, e, f])

def nu2 (w : List Bool) : Nat :=
  match w with
  | [] => 0
  | a :: wa =>
      match wa with
      | [] => 0
      | b :: wb =>
          match wb with
          | [] => 0
          | c :: wc =>
              match wc with
              | [] => 0
              | d :: wd =>
                  match wd with
                  | [] => 0
                  | e :: we =>
                      match we with
                      | [] => 0
                      | f :: rest =>
                          hit6 a b c d e f + nu2 (b :: c :: d :: e :: f :: rest)

def pref5 : List Bool → List Bool
  | [] => []
  | a :: xs =>
      match xs with
      | [] => [a]
      | b :: ys =>
          match ys with
          | [] => [a, b]
          | c :: zs =>
              match zs with
              | [] => [a, b, c]
              | d :: us =>
                  match us with
                  | [] => [a, b, c, d]
                  | e :: _ => [a, b, c, d, e]

def suf5 : List Bool → List Bool
  | [] => []
  | a :: xs =>
      match xs with
      | [] => [a]
      | b :: ys =>
          match ys with
          | [] => [a, b]
          | c :: zs =>
              match zs with
              | [] => [a, b, c]
              | d :: us =>
                  match us with
                  | [] => [a, b, c, d]
                  | e :: vs =>
                      match vs with
                      | [] => [a, b, c, d, e]
                      | _ :: _ => suf5 xs

def straddle (s t : List Bool) : Nat :=
  match s with
  | [] => 0
  | s0 :: ss0 =>
      match ss0 with
      | [] => 0
      | s1 :: ss1 =>
          match ss1 with
          | [] => 0
          | s2 :: ss2 =>
              match ss2 with
              | [] => 0
              | s3 :: ss3 =>
                  match ss3 with
                  | [] => 0
                  | s4 :: srest =>
                      match srest with
                      | [] =>
                          match t with
                          | [] => 0
                          | t0 :: tt0 =>
                              match tt0 with
                              | [] => 0
                              | t1 :: tt1 =>
                                  match tt1 with
                                  | [] => 0
                                  | t2 :: tt2 =>
                                      match tt2 with
                                      | [] => 0
                                      | t3 :: tt3 =>
                                          match tt3 with
                                          | [] => 0
                                          | t4 :: trest =>
                                              match trest with
                                              | [] =>
                                                  hit6 s0 s1 s2 s3 s4 t0 +
                                                    (hit6 s1 s2 s3 s4 t0 t1 +
                                                      (hit6 s2 s3 s4 t0 t1 t2 +
                                                        (hit6 s3 s4 t0 t1 t2 t3 +
                                                          hit6 s4 t0 t1 t2 t3 t4)))
                                              | _ :: _ => 0
                      | _ :: _ => 0

theorem add_assoc_pure (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero =>
      rfl
  | succ c ih =>
      change Nat.succ ((a + b) + c) = Nat.succ (a + (b + c))
      rw [ih]

theorem add_zero_pure (a : Nat) : a + 0 = a := by
  rfl

theorem zero_add_pure (a : Nat) : 0 + a = a := by
  induction a with
  | zero =>
      rfl
  | succ a ih =>
      change Nat.succ (0 + a) = Nat.succ a
      rw [ih]

theorem add_succ_pure (a b : Nat) : a + Nat.succ b = Nat.succ (a + b) := by
  rfl

theorem succ_add_pure (a b : Nat) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero =>
      rfl
  | succ b ih =>
      change Nat.succ (Nat.succ a + b) = Nat.succ (Nat.succ (a + b))
      rw [ih]

theorem add_comm_pure (a b : Nat) : a + b = b + a := by
  induction b with
  | zero =>
      rw [add_zero_pure a, zero_add_pure a]
  | succ b ih =>
      rw [add_succ_pure a b, succ_add_pure b a, ih]

theorem add_front_three (a b c d : Nat) :
    a + (b + c + d) = a + b + c + d := by
  rw [← add_assoc_pure a (b + c) d]
  rw [← add_assoc_pure a b c]

theorem add_rotate_five (n a b c d e : Nat) :
    a + (b + (c + (d + (e + n)))) =
      n + (a + (b + (c + (d + e)))) := by
  rw [← add_assoc_pure d e n]
  rw [← add_assoc_pure c (d + e) n]
  rw [← add_assoc_pure b (c + (d + e)) n]
  rw [← add_assoc_pure a (b + (c + (d + e))) n]
  rw [add_comm_pure (a + (b + (c + (d + e)))) n]

theorem le_pred (a b : Nat) (h : Nat.succ a ≤ Nat.succ b) : a ≤ b := by
  exact Nat.le_of_succ_le_succ h

theorem false_five_le_zero (h : 5 ≤ 0) : False := by
  exact Nat.not_succ_le_zero 4 h

theorem false_five_le_one (h : 5 ≤ 1) : False := by
  exact Nat.not_succ_le_zero 3 (le_pred 4 0 h)

theorem false_five_le_two (h : 5 ≤ 2) : False := by
  exact Nat.not_succ_le_zero 2 (le_pred 3 0 (le_pred 4 1 h))

theorem false_five_le_three (h : 5 ≤ 3) : False := by
  exact Nat.not_succ_le_zero 1 (le_pred 2 0 (le_pred 3 1 (le_pred 4 2 h)))

theorem false_five_le_four (h : 5 ≤ 4) : False := by
  exact Nat.not_succ_le_zero 0
    (le_pred 1 0 (le_pred 2 1 (le_pred 3 2 (le_pred 4 3 h))))

theorem append_base_five
    (a b c d e : Bool) (y : List Bool) (hy : 5 ≤ y.length) :
    nu2 ((a :: b :: c :: d :: e :: []) ++ y) =
      nu2 (a :: b :: c :: d :: e :: []) + nu2 y +
        straddle (suf5 (a :: b :: c :: d :: e :: [])) (pref5 y) := by
  cases y with
  | nil =>
      exact False.elim (false_five_le_zero hy)
  | cons t0 y1 =>
      cases y1 with
      | nil =>
          exact False.elim (false_five_le_one hy)
      | cons t1 y2 =>
          cases y2 with
          | nil =>
              exact False.elim (false_five_le_two hy)
          | cons t2 y3 =>
              cases y3 with
              | nil =>
                  exact False.elim (false_five_le_three hy)
              | cons t3 y4 =>
                  cases y4 with
                  | nil =>
                      exact False.elim (false_five_le_four hy)
                  | cons t4 rest =>
                      change
                        hit6 a b c d e t0 +
                          (hit6 b c d e t0 t1 +
                            (hit6 c d e t0 t1 t2 +
                              (hit6 d e t0 t1 t2 t3 +
                                (hit6 e t0 t1 t2 t3 t4 +
                                  nu2 (t0 :: t1 :: t2 :: t3 :: t4 :: rest))))) =
                        0 + nu2 (t0 :: t1 :: t2 :: t3 :: t4 :: rest) +
                          (hit6 a b c d e t0 +
                            (hit6 b c d e t0 t1 +
                              (hit6 c d e t0 t1 t2 +
                                (hit6 d e t0 t1 t2 t3 +
                                  hit6 e t0 t1 t2 t3 t4))))
                      rw [add_rotate_five
                        (nu2 (t0 :: t1 :: t2 :: t3 :: t4 :: rest))
                        (hit6 a b c d e t0)
                        (hit6 b c d e t0 t1)
                        (hit6 c d e t0 t1 t2)
                        (hit6 d e t0 t1 t2 t3)
                        (hit6 e t0 t1 t2 t3 t4)]
                      rw [zero_add_pure
                        (nu2 (t0 :: t1 :: t2 :: t3 :: t4 :: rest))]

theorem append_core_five
    (a b c d e : Bool) (tail y : List Bool) (hy : 5 ≤ y.length) :
    nu2 ((a :: b :: c :: d :: e :: tail) ++ y) =
      nu2 (a :: b :: c :: d :: e :: tail) + nu2 y +
        straddle (suf5 (a :: b :: c :: d :: e :: tail)) (pref5 y) := by
  induction tail generalizing a b c d e with
  | nil =>
      exact append_base_five a b c d e y hy
  | cons f rest ih =>
      change
        hit6 a b c d e f + nu2 ((b :: c :: d :: e :: f :: rest) ++ y) =
          hit6 a b c d e f +
            nu2 (b :: c :: d :: e :: f :: rest) + nu2 y +
              straddle (suf5 (b :: c :: d :: e :: f :: rest)) (pref5 y)
      rw [ih b c d e f]
      rw [add_front_three
        (hit6 a b c d e f)
        (nu2 (b :: c :: d :: e :: f :: rest))
        (nu2 y)
        (straddle (suf5 (b :: c :: d :: e :: f :: rest)) (pref5 y))]

theorem window6_seam_scanner_append
    (x y : List Bool) (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) :
    nu2 (x ++ y) =
      nu2 x + nu2 y + straddle (suf5 x) (pref5 y) := by
  cases x with
  | nil =>
      exact False.elim (false_five_le_zero hx)
  | cons a x1 =>
      cases x1 with
      | nil =>
          exact False.elim (false_five_le_one hx)
      | cons b x2 =>
          cases x2 with
          | nil =>
              exact False.elim (false_five_le_two hx)
          | cons c x3 =>
              cases x3 with
              | nil =>
                  exact False.elim (false_five_le_three hx)
              | cons d x4 =>
                  cases x4 with
                  | nil =>
                      exact False.elim (false_five_le_four hx)
                  | cons e tail =>
                      exact append_core_five a b c d e tail y hy

def bxor : Bool → Bool → Bool
  | false, b => b
  | true, b => !b

def parity : Nat → Bool
  | 0 => false
  | n + 1 => !(parity n)

theorem parity_succ (n : Nat) :
    parity (Nat.succ n) = !(parity n) := by
  rfl

theorem bxor_false_left (b : Bool) : bxor false b = b := by
  rfl

theorem bxor_succ_left (a b : Bool) :
    bxor (!a) b = !(bxor a b) := by
  cases a
  · cases b
    · rfl
    · rfl
  · cases b
    · rfl
    · rfl

theorem bxor_false_right (a : Bool) :
    bxor a false = a := by
  cases a
  · rfl
  · rfl

theorem bxor_not_right (a b : Bool) :
    bxor a (!b) = !(bxor a b) := by
  cases a
  · cases b
    · rfl
    · rfl
  · cases b
    · rfl
    · rfl

theorem parity_add (a b : Nat) :
    parity (a + b) = bxor (parity a) (parity b) := by
  induction b with
  | zero =>
      change parity (a + 0) = bxor (parity a) false
      rw [add_zero_pure a, bxor_false_right]
  | succ b ih =>
      rw [add_succ_pure a b]
      rw [parity_succ (a + b), parity_succ b]
      rw [ih]
      rw [bxor_not_right]

theorem window6_seam_scanner_append_parity
    (x y : List Bool) (hx : 5 ≤ x.length) (hy : 5 ≤ y.length) :
    parity (nu2 (x ++ y)) =
      bxor (bxor (parity (nu2 x)) (parity (nu2 y)))
        (parity (straddle (suf5 x) (pref5 y))) := by
  rw [window6_seam_scanner_append x y hx hy]
  rw [parity_add (nu2 x + nu2 y) (straddle (suf5 x) (pref5 y))]
  rw [parity_add (nu2 x) (nu2 y)]

def appendLists {α : Type} : List (List α) → List α
  | [] => []
  | xs :: rest => xs ++ appendLists rest

def flatMapList {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => f x ++ flatMapList f xs

def allWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 =>
      flatMapList
        (fun w => [false :: w, true :: w])
        (allWords n)

def filterBool {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
      match p x with
      | true => x :: filterBool p xs
      | false => filterBool p xs

def gamma (m : Nat) : List (List Bool) :=
  filterBool noAdj (allWords m)

def evenNu2 (w : List Bool) : Bool :=
  !(parity (nu2 w))

def R (m : Nat) : Nat :=
  (filterBool evenNu2 (gamma m)).length

theorem R_six : R 6 = 11 := by
  rfl

theorem R_seven : R 7 = 20 := by
  rfl

def xs_five : List Bool := [false, true, false, false, true]
def ys_five : List Bool := [false, false, true, false, false]
def xs_six : List Bool := [true, false, false, true, false, false]
def ys_six : List Bool := [false, true, false, false, false, true]

theorem concrete_append_five :
    nu2 (xs_five ++ ys_five) =
      nu2 xs_five + nu2 ys_five + straddle (suf5 xs_five) (pref5 ys_five) := by
  rfl

theorem concrete_append_six :
    nu2 (xs_six ++ ys_six) =
      nu2 xs_six + nu2 ys_six + straddle (suf5 xs_six) (pref5 ys_six) := by
  rfl

theorem concrete_append_six_value :
    nu2 (xs_six ++ ys_six) = 4 := by
  rfl

end BEDC.Derived.Window6SeamGluingParity
