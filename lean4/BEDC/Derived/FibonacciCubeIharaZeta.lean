/-
Fibonacci-cube Ihara zeta certificate.

For the Fibonacci-cube graph Gamma_m, whose vertices are length-m binary
words with no adjacent 1s and whose edges join Hamming-distance-one words,
the Ihara zeta reciprocal is governed by Bass' determinant

  Z_Gamma(u)^(-1) = (1 - u^2)^(|E| - |V|)
    det(I - A u + (D - I) u^2).

This file records the finite polynomial determinant identities for Gamma_1,
Gamma_2, and Gamma_3.  Gamma_3 is the first non-tree case:

  det(I - A u + (D - I) u^2) = 1 - 2 u^4 + u^8
    = (u - 1)^2 (u + 1)^2 (u^2 + 1)^2.

This is a finite graph-zeta certificate in the graph-RH/Ramanujan analogy.
It is not the actual Riemann xi function and is not a proof of the Riemann
Hypothesis.
-/

namespace BEDC.Derived.FibonacciCubeIharaZeta

abbrev UPoly := List Int

def upAllZero : UPoly -> Bool
| [] => true
| x :: xs => (x == 0) && upAllZero xs

def upnorm : UPoly -> UPoly
| [] => []
| x :: xs =>
    if x == 0 then
      if upAllZero xs then [] else x :: upnorm xs
    else
      x :: upnorm xs

def upaddRaw : UPoly -> UPoly -> UPoly
| [], q => q
| p, [] => p
| x :: xs, y :: ys => (x + y) :: upaddRaw xs ys

def upadd (p q : UPoly) : UPoly :=
  upnorm (upaddRaw p q)

def upneg : UPoly -> UPoly
| [] => []
| x :: xs => (-x) :: upneg xs

def upsub (p q : UPoly) : UPoly :=
  upadd p (upneg q)

def upscale (c : Int) : UPoly -> UPoly
| [] => []
| x :: xs => (c * x) :: upscale c xs

def upmulRaw : UPoly -> UPoly -> UPoly
| [], _ => []
| x :: xs, q => upadd (upscale x q) (0 :: upmulRaw xs q)

def upmul (p q : UPoly) : UPoly :=
  upnorm (upmulRaw p q)

abbrev PMat := List (List UPoly)

def deleteCol : Nat -> List UPoly -> List UPoly
| _, [] => []
| 0, _ :: xs => xs
| j + 1, x :: xs => x :: deleteCol j xs

def minorRows (j : Nat) : PMat -> PMat
| [] => []
| row :: rows => deleteCol j row :: minorRows j rows

def pmatDetRow (minorDet : Nat -> UPoly) : List UPoly -> Nat -> UPoly
| [], _ => []
| a :: rest, j =>
    let cofactor := upmul a (minorDet j)
    let signed := if j % 2 == 0 then cofactor else upneg cofactor
    upadd signed (pmatDetRow minorDet rest (j + 1))

def pmatDetFuel : Nat -> PMat -> UPoly
| 0, [] => [1]
| 0, _ :: _ => []
| _ + 1, [] => [1]
| n + 1, row :: rows =>
    pmatDetRow (fun j => pmatDetFuel n (minorRows j rows)) row 0

def pmatDet (M : PMat) : UPoly :=
  pmatDetFuel M.length M

def fibcubeAdj_1 : List (List Int) :=
  [[0, 1],
   [1, 0]]

def fibcubeDeg_1 : List Int :=
  [1, 1]

def bassMat_1 : PMat :=
  [[[1], [0, -1]],
   [[0, -1], [1]]]

def detTarget_1 : UPoly :=
  [1, 0, -1]

def fibcubeAdj_2 : List (List Int) :=
  [[0, 1, 1],
   [1, 0, 0],
   [1, 0, 0]]

def fibcubeDeg_2 : List Int :=
  [2, 1, 1]

def bassMat_2 : PMat :=
  [[[1, 0, 1], [0, -1], [0, -1]],
   [[0, -1], [1], []],
   [[0, -1], [], [1]]]

def detTarget_2 : UPoly :=
  [1, 0, -1]

def fibcubeAdj_3 : List (List Int) :=
  [[0, 1, 1, 1, 0],
   [1, 0, 0, 0, 1],
   [1, 0, 0, 0, 0],
   [1, 0, 0, 0, 1],
   [0, 1, 0, 1, 0]]

def fibcubeDeg_3 : List Int :=
  [3, 2, 1, 2, 2]

def bassMat_3 : PMat :=
  [[[1, 0, 2], [0, -1], [0, -1], [0, -1], []],
   [[0, -1], [1, 0, 1], [], [], [0, -1]],
   [[0, -1], [], [1], [], []],
   [[0, -1], [], [], [1, 0, 1], [0, -1]],
   [[], [0, -1], [], [0, -1], [1, 0, 1]]]

def detTarget_3 : UPoly :=
  [1, 0, 0, 0, -2, 0, 0, 0, 1]

def gamma3FactoredTarget : UPoly :=
  upmul (upmul [1, -2, 1] [1, 2, 1]) [1, 0, 2, 0, 1]

def fibcubeAdj_4 : List (List Int) :=
  [[0, 1, 1, 1, 0, 1, 0, 0],
   [1, 0, 0, 0, 1, 0, 1, 0],
   [1, 0, 0, 0, 0, 0, 0, 1],
   [1, 0, 0, 0, 1, 0, 0, 0],
   [0, 1, 0, 1, 0, 0, 0, 0],
   [1, 0, 0, 0, 0, 0, 1, 1],
   [0, 1, 0, 0, 0, 1, 0, 0],
   [0, 0, 1, 0, 0, 1, 0, 0]]

def fibcubeDeg_4 : List Int :=
  [4, 3, 2, 2, 2, 3, 2, 2]

def detTarget_4 : UPoly :=
  [1, 0, 2, 0, -3, 0, -12, 0, -16, 0, -8, 0, 8, 0, 16, 0, 12]

theorem fibcube_1_adjacency_symmetric_readback :
    fibcubeAdj_1 = [[0, 1], [1, 0]] ∧ fibcubeDeg_1 = [1, 1] := by
  constructor
  · rfl
  · rfl

theorem fibcube_2_adjacency_symmetric_readback :
    fibcubeAdj_2 =
      [[0, 1, 1], [1, 0, 0], [1, 0, 0]] ∧
    fibcubeDeg_2 = [2, 1, 1] := by
  constructor
  · rfl
  · rfl

theorem fibcube_3_adjacency_symmetric_readback :
    fibcubeAdj_3 =
      [[0, 1, 1, 1, 0],
       [1, 0, 0, 0, 1],
       [1, 0, 0, 0, 0],
       [1, 0, 0, 0, 1],
       [0, 1, 0, 1, 0]] ∧
    fibcubeDeg_3 = [3, 2, 1, 2, 2] := by
  constructor
  · rfl
  · rfl

theorem fibcube_ihara_det_1 :
    (pmatDet bassMat_1 == detTarget_1) = true := by
  rfl

theorem fibcube_ihara_det_2 :
    (pmatDet bassMat_2 == detTarget_2) = true := by
  rfl

theorem fibcube_ihara_det_3 :
    (pmatDet bassMat_3 == detTarget_3) = true := by
  rfl

theorem fibcube_ihara_gamma3_factorization :
    (gamma3FactoredTarget == detTarget_3) = true := by
  rfl

theorem fibcube_ihara_zeta_recip_3 :
    (pmatDet bassMat_3 == [1, 0, 0, 0, -2, 0, 0, 0, 1]) = true := by
  rfl

/- For Gamma_1 and Gamma_2 the Bass determinant is 1 - u^2 and the exponent
|E| - |V| is negative, so the tree factor cancels in the rational Ihara
reciprocal.  This file keeps the Lean certificate at the polynomial
determinant layer and does not encode negative powers. -/
theorem fibonacci_cube_ihara_zeta_certificate :
    (pmatDet bassMat_1 == detTarget_1) = true ∧
    (pmatDet bassMat_2 == detTarget_2) = true ∧
    (pmatDet bassMat_3 == detTarget_3) = true ∧
    (gamma3FactoredTarget == detTarget_3) = true ∧
    (pmatDet bassMat_3 == [1, 0, 0, 0, -2, 0, 0, 0, 1]) = true := by
  constructor
  · exact fibcube_ihara_det_1
  constructor
  · exact fibcube_ihara_det_2
  constructor
  · exact fibcube_ihara_det_3
  constructor
  · exact fibcube_ihara_gamma3_factorization
  · exact fibcube_ihara_zeta_recip_3

end BEDC.Derived.FibonacciCubeIharaZeta
