import BEDC.Real.RatInterval

set_option maxHeartbeats 20000000
set_option maxRecDepth 4096

/-!
Computational core of the strip first-zeros bound K29(t) ≥ 167/1000.
K29 = finite Herglotz-kernel sum over the first 29 Riemann-zeta zero
ordinates (LMFDB values, taken as certified rational inputs). Point
evaluations at the tangent-certificate anchor t=17.485 via kernel `rfl` on the
binary rational RatInterval.Rat. NOT RH; conditional on the 29 ordinate values.
The convexity/tangent window argument (K29(t) ≥ 167/1000 for all t∈[17,18]) is
a separate module.
-/

namespace BEDC.Derived.RHRoute.StripFirstZerosK29Core

open BEDC.Real.RatInterval
open BEDC.Real.RatInterval.RatNum

abbrev R : Type :=
  BEDC.Real.RatInterval.Rat

def aa : R :=
  div 4 5

private def sq (x : R) : R :=
  mul x x

private def denomMinus (g t : R) : R :=
  add (sq aa) (sq (sub t g))

private def denomPlus (g t : R) : R :=
  add (sq aa) (sq (add t g))

def kterm (g t : R) : R :=
  add
    (div aa (denomMinus g t))
    (div aa (denomPlus g t))

def kterm_d (g t : R) : R :=
  add
    (neg (div (mul (mul 2 aa) (sub t g))
      (sq (denomMinus g t))))
    (neg (div (mul (mul 2 aa) (add t g))
      (sq (denomPlus g t))))

def g1 : R := div 14134725142 1000000000
def g2 : R := div 21022039639 1000000000
def g3 : R := div 25010857580 1000000000
def g4 : R := div 30424876126 1000000000
def g5 : R := div 32935061588 1000000000
def g6 : R := div 37586178159 1000000000
def g7 : R := div 40918719012 1000000000
def g8 : R := div 43327073281 1000000000
def g9 : R := div 48005150881 1000000000
def g10 : R := div 49773832478 1000000000
def g11 : R := div 52970321478 1000000000
def g12 : R := div 56446247697 1000000000
def g13 : R := div 59347044003 1000000000
def g14 : R := div 60831778525 1000000000
def g15 : R := div 65112544048 1000000000
def g16 : R := div 67079810529 1000000000
def g17 : R := div 69546401711 1000000000
def g18 : R := div 72067157674 1000000000
def g19 : R := div 75704690699 1000000000
def g20 : R := div 77144840069 1000000000
def g21 : R := div 79337375020 1000000000
def g22 : R := div 82910380854 1000000000
def g23 : R := div 84735492981 1000000000
def g24 : R := div 87425274613 1000000000
def g25 : R := div 88809111208 1000000000
def g26 : R := div 92491899271 1000000000
def g27 : R := div 94651344041 1000000000
def g28 : R := div 95870634228 1000000000
def g29 : R := div 98831194218 1000000000

def K29 (t : R) : R :=
  List.foldl add (kterm g1 t)
    [ kterm g2 t
    , kterm g3 t
    , kterm g4 t
    , kterm g5 t
    , kterm g6 t
    , kterm g7 t
    , kterm g8 t
    , kterm g9 t
    , kterm g10 t
    , kterm g11 t
    , kterm g12 t
    , kterm g13 t
    , kterm g14 t
    , kterm g15 t
    , kterm g16 t
    , kterm g17 t
    , kterm g18 t
    , kterm g19 t
    , kterm g20 t
    , kterm g21 t
    , kterm g22 t
    , kterm g23 t
    , kterm g24 t
    , kterm g25 t
    , kterm g26 t
    , kterm g27 t
    , kterm g28 t
    , kterm g29 t
    ]

def K29d (t : R) : R :=
  List.foldl add (kterm_d g1 t)
    [ kterm_d g2 t
    , kterm_d g3 t
    , kterm_d g4 t
    , kterm_d g5 t
    , kterm_d g6 t
    , kterm_d g7 t
    , kterm_d g8 t
    , kterm_d g9 t
    , kterm_d g10 t
    , kterm_d g11 t
    , kterm_d g12 t
    , kterm_d g13 t
    , kterm_d g14 t
    , kterm_d g15 t
    , kterm_d g16 t
    , kterm_d g17 t
    , kterm_d g18 t
    , kterm_d g19 t
    , kterm_d g20 t
    , kterm_d g21 t
    , kterm_d g22 t
    , kterm_d g23 t
    , kterm_d g24 t
    , kterm_d g25 t
    , kterm_d g26 t
    , kterm_d g27 t
    , kterm_d g28 t
    , kterm_d g29 t
    ]

def cMin : R :=
  div 3497 200

theorem K29_cMin_lb :
    (div 167099 1000000 : R) <= K29 cMin :=
  qLe_of_qLeBool
    (show qLeBool (div 167099 1000000) (K29 cMin) = true by
      rfl)

theorem K29d_cMin_ub :
    K29d cMin <= (div 1 1000000 : R) :=
  qLe_of_qLeBool
    (show qLeBool (K29d cMin) (div 1 1000000) = true by
      rfl)

theorem K29d_cMin_lb :
    (neg (div 1 1000000) : R) <= K29d cMin :=
  qLe_of_qLeBool
    (show qLeBool (neg (div 1 1000000)) (K29d cMin) = true by
      rfl)

end BEDC.Derived.RHRoute.StripFirstZerosK29Core
