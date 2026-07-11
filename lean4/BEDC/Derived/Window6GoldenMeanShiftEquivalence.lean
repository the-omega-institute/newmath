import BEDC.Derived.Window6GoldenMeanRuelleZeta

namespace BEDC.Derived.Window6GoldenMeanShiftEquivalence

/-!
Golden-mean SFT zeta strong-shift-equivalence presentation certificate.

The rectangular factors `R` and `S` satisfy `RS = T_y` and `SR = E_y`,
where `T_y = [[1,y],[1,0]]` and
`E_y = [[1,y,0],[0,0,1],[1,y,0]]`.  The certificate records the common
zeta denominator `1 - t - y t^2` and the matching trace window
`tr(E_y^n) = C_n(y)` for `1 <= n <= 8`.  This is a finite presentation
invariance certificate for the golden-mean SFT zeta, not a proof of the
Riemann Hypothesis and not a statement about the Riemann xi.
-/

abbrev YPoly := Window6GoldenMeanRuelleZeta.YPoly
abbrev TPoly := Window6GoldenMeanRuelleZeta.TPoly

def padd : YPoly → YPoly → YPoly := Window6GoldenMeanRuelleZeta.padd
def pneg : YPoly → YPoly := Window6GoldenMeanRuelleZeta.pneg
def psub : YPoly → YPoly → YPoly := Window6GoldenMeanRuelleZeta.psub
def pmul : YPoly → YPoly → YPoly := Window6GoldenMeanRuelleZeta.pmul
def Cpoly : Nat → YPoly := Window6GoldenMeanRuelleZeta.Cpoly

def tadd : TPoly → TPoly → TPoly := Window6GoldenMeanRuelleZeta.tadd
def tneg : TPoly → TPoly := Window6GoldenMeanRuelleZeta.tneg
def tsub : TPoly → TPoly → TPoly := Window6GoldenMeanRuelleZeta.tsub
def tmul : TPoly → TPoly → TPoly := Window6GoldenMeanRuelleZeta.tmul

def zetaDen : TPoly := Window6GoldenMeanRuelleZeta.zetaDenTy

def zeroY : YPoly := []
def oneY : YPoly := [1]
def yY : YPoly := [0, 1]

def allZeroI : YPoly → Bool
  | [] => true
  | a :: p => (a == 0) && allZeroI p

def pnorm : YPoly → YPoly
  | [] => []
  | a :: p => if allZeroI (a :: p) then [] else a :: pnorm p

def TyMat : List (List YPoly) :=
  [[oneY, yY], [oneY, zeroY]]

def Ey : List (List YPoly) :=
  [[oneY, yY, zeroY], [zeroY, zeroY, oneY], [oneY, yY, zeroY]]

def Rmat : List (List YPoly) :=
  [[oneY, yY, zeroY], [zeroY, zeroY, oneY]]

def Smat : List (List YPoly) :=
  [[oneY, zeroY], [zeroY, oneY], [oneY, zeroY]]

def dotWith (row : List YPoly) : List YPoly → YPoly
  | [] => []
  | b :: bs =>
      match row with
      | [] => []
      | a :: as => pnorm (padd (pmul a b) (dotWith as bs))

def colHead : List (List YPoly) → List YPoly
  | [] => []
  | [] :: rows => [] :: colHead rows
  | (a :: _) :: rows => a :: colHead rows

def colTail : List (List YPoly) → List (List YPoly)
  | [] => []
  | [] :: rows => [] :: colTail rows
  | (_ :: as) :: rows => as :: colTail rows

def rowsExhausted : List (List YPoly) → Bool
  | [] => true
  | [] :: _ => true
  | (_ :: _) :: _ => false

def columnsFuel : Nat → List (List YPoly) → List (List YPoly)
  | 0, _ => []
  | n + 1, rows =>
      if rowsExhausted rows then []
      else colHead rows :: columnsFuel n (colTail rows)

def columns (rows : List (List YPoly)) : List (List YPoly) :=
  match rows with
  | [] => []
  | row :: _ => columnsFuel row.length rows

def mulRow (row : List YPoly) : List (List YPoly) → List YPoly
  | [] => []
  | col :: cols => dotWith row col :: mulRow row cols

def rmatmul (A B : List (List YPoly)) : List (List YPoly) :=
  let cols := columns B
  match A with
  | [] => []
  | row :: rows => mulRow row cols :: rmatmul rows B

theorem RS_eq_Ty : rmatmul Rmat Smat = TyMat := by
  rfl

theorem SR_eq_Ey : rmatmul Smat Rmat = Ey := by
  rfl

structure Mat2T where
  a00 : TPoly
  a01 : TPoly
  a10 : TPoly
  a11 : TPoly

structure Mat3T where
  a00 : TPoly
  a01 : TPoly
  a02 : TPoly
  a10 : TPoly
  a11 : TPoly
  a12 : TPoly
  a20 : TPoly
  a21 : TPoly
  a22 : TPoly

def det2T (M : Mat2T) : TPoly :=
  tsub (tmul M.a00 M.a11) (tmul M.a01 M.a10)

def pIsNil : YPoly → Bool
  | [] => true
  | _ :: _ => false

def allZeroT : TPoly → Bool
  | [] => true
  | a :: p => pIsNil (pnorm a) && allZeroT p

def tnorm : TPoly → TPoly
  | [] => []
  | a :: p => if allZeroT (a :: p) then [] else a :: tnorm p

def det3RawT (M : Mat3T) : TPoly :=
  tadd
    (tadd (tmul M.a00 (tmul M.a11 M.a22)) (tmul M.a01 (tmul M.a12 M.a20)))
    (tadd
      (tmul M.a02 (tmul M.a10 M.a21))
      (tneg
        (tadd
          (tadd (tmul M.a02 (tmul M.a11 M.a20)) (tmul M.a01 (tmul M.a10 M.a22)))
          (tmul M.a00 (tmul M.a12 M.a21)))))

def det3T (M : Mat3T) : TPoly :=
  tnorm (det3RawT M)

def IMinus_tTy : Mat2T :=
  Mat2T.mk [[1], [-1]] [[], [0, -1]] [[], [-1]] [[1]]

def IMinus_tEy : Mat3T :=
  Mat3T.mk
    [[1], [-1]] [[], [0, -1]] []
    [] [[1]] [[], [-1]]
    [[], [-1]] [[], [0, -1]] [[1]]

theorem det_two_presentation : det2T IMinus_tTy = zetaDen := by
  rfl

theorem det_three_presentation : det3T IMinus_tEy = zetaDen := by
  rfl

theorem presentation_determinant_invariance :
    det2T IMinus_tTy = det3T IMinus_tEy := by
  rfl

structure Mat3Y where
  a00 : YPoly
  a01 : YPoly
  a02 : YPoly
  a10 : YPoly
  a11 : YPoly
  a12 : YPoly
  a20 : YPoly
  a21 : YPoly
  a22 : YPoly

def EyMat3 : Mat3Y :=
  Mat3Y.mk oneY yY zeroY zeroY zeroY oneY oneY yY zeroY

def I3Y : Mat3Y :=
  Mat3Y.mk oneY zeroY zeroY zeroY oneY zeroY zeroY zeroY oneY

def madd3 (A B : Mat3Y) : Mat3Y :=
  Mat3Y.mk
    (padd A.a00 B.a00) (padd A.a01 B.a01) (padd A.a02 B.a02)
    (padd A.a10 B.a10) (padd A.a11 B.a11) (padd A.a12 B.a12)
    (padd A.a20 B.a20) (padd A.a21 B.a21) (padd A.a22 B.a22)

def mmul3 (A B : Mat3Y) : Mat3Y :=
  Mat3Y.mk
    (padd (padd (pmul A.a00 B.a00) (pmul A.a01 B.a10)) (pmul A.a02 B.a20))
    (padd (padd (pmul A.a00 B.a01) (pmul A.a01 B.a11)) (pmul A.a02 B.a21))
    (padd (padd (pmul A.a00 B.a02) (pmul A.a01 B.a12)) (pmul A.a02 B.a22))
    (padd (padd (pmul A.a10 B.a00) (pmul A.a11 B.a10)) (pmul A.a12 B.a20))
    (padd (padd (pmul A.a10 B.a01) (pmul A.a11 B.a11)) (pmul A.a12 B.a21))
    (padd (padd (pmul A.a10 B.a02) (pmul A.a11 B.a12)) (pmul A.a12 B.a22))
    (padd (padd (pmul A.a20 B.a00) (pmul A.a21 B.a10)) (pmul A.a22 B.a20))
    (padd (padd (pmul A.a20 B.a01) (pmul A.a21 B.a11)) (pmul A.a22 B.a21))
    (padd (padd (pmul A.a20 B.a02) (pmul A.a21 B.a12)) (pmul A.a22 B.a22))

def mpow3 : Nat → Mat3Y
  | 0 => I3Y
  | n + 1 => mmul3 (mpow3 n) EyMat3

def tr3 (M : Mat3Y) : YPoly :=
  padd (padd M.a00 M.a11) M.a22

theorem trace_invariance_one : tr3 (mpow3 1) = Cpoly 1 := by
  rfl

theorem trace_invariance_two : tr3 (mpow3 2) = Cpoly 2 := by
  rfl

theorem trace_invariance_three : tr3 (mpow3 3) = Cpoly 3 := by
  rfl

theorem trace_invariance_four : tr3 (mpow3 4) = Cpoly 4 := by
  rfl

theorem trace_invariance_five : tr3 (mpow3 5) = Cpoly 5 := by
  rfl

theorem trace_invariance_six : tr3 (mpow3 6) = Cpoly 6 := by
  rfl

theorem trace_invariance_seven : tr3 (mpow3 7) = Cpoly 7 := by
  rfl

theorem trace_invariance_eight : tr3 (mpow3 8) = Cpoly 8 := by
  rfl

theorem trace_six_concrete : tr3 (mpow3 6) = [1, 6, 9, 2] := by
  rfl

theorem trace_eight_concrete : tr3 (mpow3 8) = [1, 8, 20, 16, 2] := by
  rfl

theorem golden_mean_shift_equivalence_certificate :
    (rmatmul Rmat Smat = TyMat) ∧
      (rmatmul Smat Rmat = Ey) ∧
      (det2T IMinus_tTy = zetaDen) ∧
      (det3T IMinus_tEy = zetaDen) ∧
      (det2T IMinus_tTy = det3T IMinus_tEy) ∧
      (tr3 (mpow3 1) = Cpoly 1) ∧
      (tr3 (mpow3 2) = Cpoly 2) ∧
      (tr3 (mpow3 3) = Cpoly 3) ∧
      (tr3 (mpow3 4) = Cpoly 4) ∧
      (tr3 (mpow3 5) = Cpoly 5) ∧
      (tr3 (mpow3 6) = Cpoly 6) ∧
      (tr3 (mpow3 7) = Cpoly 7) ∧
      (tr3 (mpow3 8) = Cpoly 8) := by
  exact
    And.intro rfl
      (And.intro rfl
        (And.intro rfl
          (And.intro rfl
            (And.intro rfl
              (And.intro rfl
                (And.intro rfl
                  (And.intro rfl
                    (And.intro rfl
                      (And.intro rfl
                        (And.intro rfl
                          (And.intro rfl rfl)))))))))))

end BEDC.Derived.Window6GoldenMeanShiftEquivalence
