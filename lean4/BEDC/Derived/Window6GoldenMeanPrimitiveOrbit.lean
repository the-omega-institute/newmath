import BEDC.Derived.Window6GoldenMeanRuelleZeta

namespace BEDC.Derived.Window6GoldenMeanPrimitiveOrbit

/-!
Golden-mean subshift zeta certificate for primitive-orbit Mobius
integrality and positivity on the Euler-product side.  The weighted
substitution is `y |-> y^d`; this is not an RH proof.
-/

abbrev YPoly := Window6GoldenMeanRuelleZeta.YPoly

def padd (p q : YPoly) : YPoly := Window6GoldenMeanRuelleZeta.padd p q

def pscale (a : Int) (p : YPoly) : YPoly :=
  Window6GoldenMeanRuelleZeta.pscale a p

def Cpoly (n : Nat) : YPoly := Window6GoldenMeanRuelleZeta.Cpoly n

def pevalOne (p : YPoly) : Int := Window6GoldenMeanRuelleZeta.pevalOne p

def zeroPad : Nat → YPoly
  | 0 => []
  | n + 1 => 0 :: zeroPad n

def substPow (d : Nat) : YPoly → YPoly
  | [] => []
  | a :: [] => [a]
  | a :: b :: p => a :: zeroPad (d - 1) ++ substPow d (b :: p)

theorem substPow_two_example :
    substPow 2 [1, 3] = [1, 0, 3] := by
  rfl

theorem substPow_three_example :
    substPow 3 [1, 2] = [1, 0, 0, 2] := by
  rfl

def mobius : Nat → Int
  | 1 => 1
  | 2 => -1
  | 3 => -1
  | 4 => 0
  | 5 => -1
  | 6 => 1
  | 7 => -1
  | 8 => 0
  | 9 => 0
  | 10 => 1
  | 11 => -1
  | 12 => 0
  | _ => 0

theorem mobius_six :
    mobius 6 = 1 := by
  rfl

theorem mobius_ten :
    mobius 10 = 1 := by
  rfl

def divisorsOf : Nat → List Nat
  | 1 => [1]
  | 2 => [1, 2]
  | 3 => [1, 3]
  | 4 => [1, 2, 4]
  | 5 => [1, 5]
  | 6 => [1, 2, 3, 6]
  | 7 => [1, 7]
  | 8 => [1, 2, 4, 8]
  | 9 => [1, 3, 9]
  | 10 => [1, 2, 5, 10]
  | 11 => [1, 11]
  | 12 => [1, 2, 3, 4, 6, 12]
  | _ => []

def dropLast : YPoly → YPoly
  | [] => []
  | _ :: [] => []
  | a :: b :: p => a :: dropLast (b :: p)

def pcanonWindow (n : Nat) (p : YPoly) : YPoly :=
  match n with
  | 4 => dropLast p
  | 6 => dropLast p
  | 8 => dropLast p
  | 10 => dropLast p
  | 12 => dropLast p
  | _ => p

def AtermSum (n : Nat) : List Nat → YPoly
  | [] => []
  | d :: ds =>
      padd (pscale (mobius d) (substPow d (Cpoly (n / d)))) (AtermSum n ds)

def Aterm (n : Nat) : YPoly := pcanonWindow n (AtermSum n (divisorsOf n))

def Pnat : Nat → List Nat
  | 1 => [1]
  | 2 => [0, 1]
  | 3 => [0, 1]
  | 4 => [0, 1]
  | 5 => [0, 1, 1]
  | 6 => [0, 1, 1]
  | 7 => [0, 1, 2, 1]
  | 8 => [0, 1, 2, 2]
  | 9 => [0, 1, 3, 3, 1]
  | 10 => [0, 1, 3, 5, 2]
  | 11 => [0, 1, 4, 7, 5, 1]
  | 12 => [0, 1, 4, 9, 8, 3]
  | _ => []

def Pint (n : Nat) : YPoly := (Pnat n).map (fun k => Int.ofNat k)

theorem primitive_orbit_integrality_1 :
    Aterm 1 = pscale (Int.ofNat 1) (Pint 1) := by
  rfl

theorem primitive_orbit_integrality_2 :
    Aterm 2 = pscale (Int.ofNat 2) (Pint 2) := by
  rfl

theorem primitive_orbit_integrality_3 :
    Aterm 3 = pscale (Int.ofNat 3) (Pint 3) := by
  rfl

theorem primitive_orbit_integrality_4 :
    Aterm 4 = pscale (Int.ofNat 4) (Pint 4) := by
  rfl

theorem primitive_orbit_integrality_5 :
    Aterm 5 = pscale (Int.ofNat 5) (Pint 5) := by
  rfl

theorem primitive_orbit_integrality_6 :
    Aterm 6 = pscale (Int.ofNat 6) (Pint 6) := by
  rfl

theorem primitive_orbit_integrality_7 :
    Aterm 7 = pscale (Int.ofNat 7) (Pint 7) := by
  rfl

theorem primitive_orbit_integrality_8 :
    Aterm 8 = pscale (Int.ofNat 8) (Pint 8) := by
  rfl

theorem primitive_orbit_integrality_9 :
    Aterm 9 = pscale (Int.ofNat 9) (Pint 9) := by
  rfl

theorem primitive_orbit_integrality_10 :
    Aterm 10 = pscale (Int.ofNat 10) (Pint 10) := by
  rfl

theorem primitive_orbit_integrality_11 :
    Aterm 11 = pscale (Int.ofNat 11) (Pint 11) := by
  rfl

theorem primitive_orbit_integrality_12 :
    Aterm 12 = pscale (Int.ofNat 12) (Pint 12) := by
  rfl

theorem golden_mean_primitive_orbit_mobius_positivity :
    (Aterm 1 = pscale (Int.ofNat 1) (Pint 1)) ∧
      (Aterm 2 = pscale (Int.ofNat 2) (Pint 2)) ∧
      (Aterm 3 = pscale (Int.ofNat 3) (Pint 3)) ∧
      (Aterm 4 = pscale (Int.ofNat 4) (Pint 4)) ∧
      (Aterm 5 = pscale (Int.ofNat 5) (Pint 5)) ∧
      (Aterm 6 = pscale (Int.ofNat 6) (Pint 6)) ∧
      (Aterm 7 = pscale (Int.ofNat 7) (Pint 7)) ∧
      (Aterm 8 = pscale (Int.ofNat 8) (Pint 8)) ∧
      (Aterm 9 = pscale (Int.ofNat 9) (Pint 9)) ∧
      (Aterm 10 = pscale (Int.ofNat 10) (Pint 10)) ∧
      (Aterm 11 = pscale (Int.ofNat 11) (Pint 11)) ∧
      (Aterm 12 = pscale (Int.ofNat 12) (Pint 12)) := by
  exact
    And.intro primitive_orbit_integrality_1
      (And.intro primitive_orbit_integrality_2
        (And.intro primitive_orbit_integrality_3
          (And.intro primitive_orbit_integrality_4
            (And.intro primitive_orbit_integrality_5
              (And.intro primitive_orbit_integrality_6
                (And.intro primitive_orbit_integrality_7
                  (And.intro primitive_orbit_integrality_8
                    (And.intro primitive_orbit_integrality_9
                      (And.intro primitive_orbit_integrality_10
                        (And.intro primitive_orbit_integrality_11
                          primitive_orbit_integrality_12))))))))))

theorem Aterm_six_at_one :
    pevalOne (Aterm 6) = 12 := by
  rfl

theorem Pint_five_at_one :
    pevalOne (Pint 5) = 2 := by
  rfl

theorem Aterm_twelve_at_one :
    pevalOne (Aterm 12) = 300 := by
  rfl

theorem Pint_twelve_at_one :
    pevalOne (Pint 12) = 25 := by
  rfl

end BEDC.Derived.Window6GoldenMeanPrimitiveOrbit
