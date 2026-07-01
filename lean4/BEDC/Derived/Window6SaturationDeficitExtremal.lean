namespace BEDC.Derived.Window6SaturationDeficitExtremal

/-!
Sharp two-sided inequality and extremal-witness package for the length-six
saturation deficit, separate from recurrence, trace, congruence, gluing, and
minimum-degree anchors.
-/

def noAdj : List Bool → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!(a && b)) && noAdj (b :: rest)

def bitLoad : Bool → Nat
  | false => 0
  | true => 1

def load6 (a b c d e f : Bool) : Nat :=
  bitLoad a + bitLoad b + bitLoad c + bitLoad d + bitLoad e + bitLoad f

def headDeficit (a b c d e f : Bool) : Nat :=
  3 - load6 a b c d e f

def deficit6 : List Bool → Nat
  | [] => 0
  | [_] => 0
  | [_, _] => 0
  | [_, _, _] => 0
  | [_, _, _, _] => 0
  | [_, _, _, _, _] => 0
  | a :: b :: c :: d :: e :: f :: rest =>
      headDeficit a b c d e f + deficit6 (b :: c :: d :: e :: f :: rest)

def N6 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n))))) =>
      Nat.succ (N6 (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ n))))))

theorem headDeficit_le_three (a b c d e f : Bool) :
    headDeficit a b c d e f ≤ 3 :=
  Nat.sub_le 3 (load6 a b c d e f)

theorem add_head_tail_le_three_mul_succ {h t n : Nat}
    (hh : h ≤ 3) (ht : t ≤ 3 * n) :
    h + t ≤ 3 * Nat.succ n := by
  rw [Nat.mul_succ]
  rw [Nat.add_comm (3 * n) 3]
  exact Nat.add_le_add hh ht

theorem window6_saturation_deficit_upper (w : List Bool) :
    deficit6 w ≤ 3 * N6 w.length := by
  induction w with
  | nil =>
      exact Nat.le.refl
  | cons a rest ih =>
      cases rest with
      | nil =>
          exact Nat.le.refl
      | cons b rest =>
          cases rest with
          | nil =>
              exact Nat.le.refl
          | cons c rest =>
              cases rest with
              | nil =>
                  exact Nat.le.refl
              | cons d rest =>
                  cases rest with
                  | nil =>
                      exact Nat.le.refl
                  | cons e rest =>
                      cases rest with
                      | nil =>
                          exact Nat.le.refl
                      | cons f rest =>
                          change
                            headDeficit a b c d e f +
                                deficit6 (b :: c :: d :: e :: f :: rest)
                              ≤ 3 *
                                Nat.succ
                                  (N6 (b :: c :: d :: e :: f :: rest).length)
                          exact
                            add_head_tail_le_three_mul_succ
                              (headDeficit_le_three a b c d e f)
                              ih

theorem window6_saturation_deficit_lower (w : List Bool) :
    0 ≤ deficit6 w :=
  Nat.zero_le (deficit6 w)

def allZeros : Nat → List Bool
  | 0 => []
  | Nat.succ n => false :: allZeros n

theorem window6_deficit_allzeros (m : Nat) :
    deficit6 (allZeros m) = 3 * N6 m := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      cases m with
      | zero =>
          rfl
      | succ m =>
          cases m with
          | zero =>
              rfl
          | succ m =>
              cases m with
              | zero =>
                  rfl
              | succ m =>
                  cases m with
                  | zero =>
                      rfl
                  | succ m =>
                      cases m with
                      | zero =>
                          rfl
                      | succ m =>
                          change
                            3 + deficit6 (allZeros (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ m))))))
                              =
                            3 *
                              Nat.succ
                                (N6 (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ m))))))
                          rw [ih]
                          rw [Nat.mul_succ]
                          rw [Nat.add_comm (3 * N6 (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ m)))))) 3]

def altFrom : Bool → Nat → List Bool
  | _, 0 => []
  | b, Nat.succ n => b :: altFrom (!b) n

theorem window6_deficit_alt (b : Bool) (m : Nat) :
    deficit6 (altFrom b m) = 0 := by
  induction m generalizing b with
  | zero =>
      rfl
  | succ m ih =>
      cases m with
      | zero =>
          cases b <;> rfl
      | succ m =>
          cases m with
          | zero =>
              cases b <;> rfl
          | succ m =>
              cases m with
              | zero =>
                  cases b <;> rfl
              | succ m =>
                  cases m with
                  | zero =>
                      cases b <;> rfl
                  | succ m =>
                      cases m with
                      | zero =>
                          cases b <;> rfl
                      | succ m =>
                          cases b
                          · change 0 + deficit6 (altFrom true (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ m)))))) = 0
                            rw [ih true]
                          · change 0 + deficit6 (altFrom false (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ m)))))) = 0
                            rw [ih false]

theorem deficit6_allZeros_six : deficit6 (allZeros 6) = 3 := by
  rfl

theorem deficit6_alt_true_six :
    deficit6 [true, false, true, false, true, false] = 0 := by
  rfl

end BEDC.Derived.Window6SaturationDeficitExtremal
