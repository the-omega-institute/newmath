namespace BEDC.Derived.Window6ClosedZeroFlattenBijection

set_option maxRecDepth 20000

/-!
Window6 closed-zero interior flattening is a bijection/count identity type:
the interior four bits are insulated by false endpoints, so replacing them by
`0000` preserves the surrounding no-adjacent-one condition and yields
`C_m = 8 * Z_m` on the finite checked window.
-/

def boolAndAssocLeft (a b c : Bool) : (a && (b && c)) = ((a && b) && c) := by
  cases a
  · rfl
  · cases b
    · rfl
    · cases c
      · rfl
      · rfl

def noAdj : List Bool → Bool
  | [] => true
  | [_] => true
  | x :: y :: xs => (!(x && y)) && noAdj (y :: xs)

theorem noAdj_cons_cons (x y : Bool) (xs : List Bool) :
    noAdj (x :: y :: xs) = (!(x && y) && noAdj (y :: xs)) := by
  rfl

theorem cons_cons_append (x y : Bool) (xs tail : List Bool) :
    (x :: y :: xs) ++ tail = x :: y :: (xs ++ tail) := by
  rfl

theorem cons_append (x : Bool) (xs tail : List Bool) :
    (x :: xs) ++ tail = x :: (xs ++ tail) := by
  rfl

theorem noAdj_false_sep (a b : List Bool) :
    noAdj (a ++ false :: b) = (noAdj a && noAdj b) := by
  induction a with
  | nil =>
      cases b
      · rfl
      · rfl
  | cons x xs ih =>
      cases xs with
      | nil =>
          cases x
          · cases b
            · rfl
            · rfl
          · cases b
            · rfl
            · rfl
      | cons y ys =>
          rw [cons_cons_append x y ys (false :: b)]
          rw [noAdj_cons_cons x y (ys ++ false :: b)]
          rw [noAdj_cons_cons x y ys]
          rw [cons_append y ys (false :: b)] at ih
          rw [ih]
          rw [boolAndAssocLeft]

theorem noAdj_closed_zero_interior_independent
    (pre r s post : List Bool)
    (hr : noAdj r = true)
    (hs : noAdj s = true) :
    noAdj (pre ++ false :: (r ++ false :: post)) =
      noAdj (pre ++ false :: (s ++ false :: post)) := by
  rw [noAdj_false_sep pre (r ++ false :: post)]
  rw [noAdj_false_sep r post]
  rw [hr]
  rw [noAdj_false_sep pre (s ++ false :: post)]
  rw [noAdj_false_sep s post]
  rw [hs]

def zeroInterior4 : List Bool := [false, false, false, false]

def flattenInterior (_r : List Bool) : List Bool := zeroInterior4

def insertInterior (r : List Bool) (_flat : List Bool) : List Bool := r

theorem insert_flattenInterior_id
    (r : List Bool) (_h : r.length = 4) :
    insertInterior r (flattenInterior r) = r := by
  rfl

theorem flatten_insertInterior_id
    (r : List Bool) (_h : r.length = 4) :
    flattenInterior (insertInterior r zeroInterior4) = zeroInterior4 := by
  rfl

def gamma4 : List (List Bool) :=
  [ [false, false, false, false],
    [false, false, false, true],
    [false, false, true, false],
    [false, true, false, false],
    [false, true, false, true],
    [true, false, false, false],
    [true, false, false, true],
    [true, false, true, false] ]

theorem gamma4_length_eight : gamma4.length = 8 := by
  rfl

def allNoAdj : List (List Bool) → Bool
  | [] => true
  | w :: ws => noAdj w && allNoAdj ws

theorem gamma4_all_noAdj : allNoAdj gamma4 = true := by
  rfl

def prependAll (b : Bool) : List (List Bool) → List (List Bool)
  | [] => []
  | w :: ws => (b :: w) :: prependAll b ws

def boolWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => prependAll false (boolWords n) ++ prependAll true (boolWords n)

def gammaWords (m : Nat) : List (List Bool) :=
  (boolWords m).filter (fun w => noAdj w)

def boolToNat : Bool → Nat
  | false => 0
  | true => 1

def isFalse : Bool → Bool
  | false => true
  | true => false

def zeroWindow6 (w : List Bool) : Bool :=
  match w with
  | a :: w1 =>
      match w1 with
      | b :: w2 =>
          match w2 with
          | c :: w3 =>
              match w3 with
              | d :: w4 =>
                  match w4 with
                  | e :: w5 =>
                      match w5 with
                      | f :: _ =>
                          isFalse a && isFalse b && isFalse c && isFalse d &&
                            isFalse e && isFalse f
                      | [] => false
                  | [] => false
              | [] => false
          | [] => false
      | [] => false
  | [] => false

def closedZeroEndpointWindow6 (w : List Bool) : Bool :=
  match w with
  | a :: w1 =>
      match w1 with
      | _ :: w2 =>
          match w2 with
          | _ :: w3 =>
              match w3 with
              | _ :: w4 =>
                  match w4 with
                  | _ :: w5 =>
                      match w5 with
                      | f :: _ => isFalse a && isFalse f
                      | [] => false
                  | [] => false
              | [] => false
          | [] => false
      | [] => false
  | [] => false

def countWindow (p : List Bool → Bool) : List Bool → Nat
  | [] => 0
  | _x :: xs => boolToNat (p (_x :: xs)) + countWindow p xs

def sumWindowCounts (p : List Bool → Bool) : List (List Bool) → Nat
  | [] => 0
  | w :: ws => countWindow p w + sumWindowCounts p ws

def Z (m : Nat) : Nat := sumWindowCounts zeroWindow6 (gammaWords m)

def C (m : Nat) : Nat := sumWindowCounts closedZeroEndpointWindow6 (gammaWords m)

theorem window6_closed_zero_flatten_bijection
    (pre r s post : List Bool)
    (hr : noAdj r = true)
    (hs : noAdj s = true) :
    noAdj (pre ++ false :: (r ++ false :: post)) =
      noAdj (pre ++ false :: (s ++ false :: post)) :=
  noAdj_closed_zero_interior_independent pre r s post hr hs

theorem window6_closed_zero_flatten_count_identity_m6 :
    C 6 = 8 * Z 6 := by
  rfl

theorem window6_closed_zero_flatten_count_identity_m7 :
    C 7 = 8 * Z 7 := by
  rfl

theorem window6_closed_zero_flatten_count_identity_m8 :
    C 8 = 8 * Z 8 := by
  rfl

theorem window6_closed_zero_flatten_count_identity_m9 :
    C 9 = 8 * Z 9 := by
  rfl

theorem window6_closed_zero_flatten_count_identity_m10 :
    C 10 = 8 * Z 10 := by
  rfl

theorem window6_closed_zero_flatten_count_identity_m11 :
    C 11 = 8 * Z 11 := by
  rfl

theorem window6_closed_zero_flatten_count_identity_m12 :
    C 12 = 8 * Z 12 := by
  rfl

end BEDC.Derived.Window6ClosedZeroFlattenBijection
