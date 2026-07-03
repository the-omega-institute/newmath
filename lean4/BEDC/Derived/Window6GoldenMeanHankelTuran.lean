import BEDC.Derived.Window6GoldenMeanRuelleZeta

namespace BEDC.Derived.Window6GoldenMeanHankelTuran

/-!
The golden-mean SFT trace sequence satisfies the finite Hankel--Turan
discriminant identity `C_n C_{n+2} - C_{n+1}^2 = (-y)^n (1 + 4y)`.
At `y = 1` this is the Lucas discriminant constant `5 * (-1)^n`;
this is a finite trace certificate, not an RH proof.
-/

abbrev YPoly := Window6GoldenMeanRuelleZeta.YPoly

def padd : YPoly → YPoly → YPoly := Window6GoldenMeanRuelleZeta.padd

def psub (p q : YPoly) : YPoly := Window6GoldenMeanRuelleZeta.psub p q

def pmul : YPoly → YPoly → YPoly := Window6GoldenMeanRuelleZeta.pmul

def pscale (a : Int) (p : YPoly) : YPoly := Window6GoldenMeanRuelleZeta.pscale a p

def pevalOne : YPoly → Int := Window6GoldenMeanRuelleZeta.pevalOne

def Cpoly : Nat → YPoly := Window6GoldenMeanRuelleZeta.Cpoly

def signPow : Nat → Int
  | 0 => 1
  | n + 1 => -signPow n

def nZeros : Nat → YPoly
  | 0 => []
  | n + 1 => 0 :: nZeros n

def turanLHS (n : Nat) : YPoly :=
  psub (pmul (Cpoly n) (Cpoly (n + 2))) (pmul (Cpoly (n + 1)) (Cpoly (n + 1)))

def turanRHS (n : Nat) : YPoly :=
  pscale (signPow n) (nZeros n ++ [1, 4])

def LucasVal (n : Nat) : Int := pevalOne (Cpoly n)

theorem hankel_turan_one : turanLHS 1 = turanRHS 1 := by
  rfl

theorem hankel_turan_two : turanLHS 2 = turanRHS 2 := by
  rfl

theorem hankel_turan_three : turanLHS 3 = turanRHS 3 := by
  rfl

theorem hankel_turan_four : turanLHS 4 = turanRHS 4 := by
  rfl

theorem hankel_turan_five : turanLHS 5 = turanRHS 5 := by
  rfl

theorem hankel_turan_six : turanLHS 6 = turanRHS 6 := by
  rfl

theorem hankel_turan_seven : turanLHS 7 = turanRHS 7 := by
  rfl

theorem hankel_turan_eight : turanLHS 8 = turanRHS 8 := by
  rfl

theorem lucas_discriminant_one :
    LucasVal 1 * LucasVal 3 - LucasVal 2 * LucasVal 2 = 5 * signPow 1 := by
  rfl

theorem lucas_discriminant_two :
    LucasVal 2 * LucasVal 4 - LucasVal 3 * LucasVal 3 = 5 * signPow 2 := by
  rfl

theorem lucas_discriminant_three :
    LucasVal 3 * LucasVal 5 - LucasVal 4 * LucasVal 4 = 5 * signPow 3 := by
  rfl

theorem lucas_discriminant_four :
    LucasVal 4 * LucasVal 6 - LucasVal 5 * LucasVal 5 = 5 * signPow 4 := by
  rfl

theorem lucas_discriminant_five :
    LucasVal 5 * LucasVal 7 - LucasVal 6 * LucasVal 6 = 5 * signPow 5 := by
  rfl

theorem lucas_discriminant_six :
    LucasVal 6 * LucasVal 8 - LucasVal 7 * LucasVal 7 = 5 * signPow 6 := by
  rfl

theorem lucas_discriminant_seven :
    LucasVal 7 * LucasVal 9 - LucasVal 8 * LucasVal 8 = 5 * signPow 7 := by
  rfl

theorem lucas_discriminant_eight :
    LucasVal 8 * LucasVal 10 - LucasVal 9 * LucasVal 9 = 5 * signPow 8 := by
  rfl

theorem turanLHS_three_coeffs : turanLHS 3 = [0, 0, 0, -1, -4] := by
  rfl

theorem turanRHS_four_coeffs : turanRHS 4 = [0, 0, 0, 0, 1, 4] := by
  rfl

theorem LucasVal_five : LucasVal 5 = 11 := by
  rfl

theorem LucasVal_eight : LucasVal 8 = 47 := by
  rfl

theorem golden_mean_hankel_turan_discriminant_certificate :
    (turanLHS 1 = turanRHS 1) ∧
      (turanLHS 2 = turanRHS 2) ∧
      (turanLHS 3 = turanRHS 3) ∧
      (turanLHS 4 = turanRHS 4) ∧
      (turanLHS 5 = turanRHS 5) ∧
      (turanLHS 6 = turanRHS 6) ∧
      (turanLHS 7 = turanRHS 7) ∧
      (turanLHS 8 = turanRHS 8) ∧
      (LucasVal 4 * LucasVal 6 - LucasVal 5 * LucasVal 5 = 5) := by
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl
        (And.intro rfl
          (And.intro rfl
            (And.intro rfl
              (And.intro rfl
                (And.intro rfl rfl)))))))

end BEDC.Derived.Window6GoldenMeanHankelTuran
