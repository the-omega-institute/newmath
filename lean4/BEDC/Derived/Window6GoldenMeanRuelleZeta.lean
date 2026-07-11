import BEDC.Derived.Window6GoldenPentagonRPLink

namespace BEDC.Derived.Window6GoldenMeanRuelleZeta

/-!
Golden-mean subshift Ruelle/Bowen-Lanford dynamical zeta certificate.

The weighted transfer matrix is `T_y = [[1,y],[1,0]]`; the cyclic
period count is `C_n(y) = tr(T_y^n)`, and the dynamical zeta is
`zeta_GM(t,y) = 1 / (1 - t - y t^2)`, with Euler product
`Pi_d (1 - t^d)^(-pi_d)`.  The finite certificate below is the
log-derivative window
`(1 - t - y t^2) S_N = 1 + 2 y t - C_{N+1} t^N - y C_N t^{N+1}`.

The golden-ring pole and spectrum statements are the Fibonacci
transfer-operator facts in `Z[phi]`: `1 - t - t^2` factors as
`(1 - phi t)(1 + (phi - 1)t)`, and the transfer spectrum is
`{phi, 1 - phi} = {phi, -phi^{-1}}`.  This is not a statement about
the Riemann zeta function, and it is not about xi; it is a finite
Fibonacci transfer certificate for the golden-mean shift zeta.
-/

abbrev YPoly := List Int

def padd : YPoly → YPoly → YPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: padd p q

def pneg : YPoly → YPoly
  | [] => []
  | a :: p => (-a) :: pneg p

def psub (p q : YPoly) : YPoly := padd p (pneg q)

def yshift (p : YPoly) : YPoly := 0 :: p

def pscale (a : Int) : YPoly → YPoly
  | [] => []
  | b :: p => (a * b) :: pscale a p

def pmul : YPoly → YPoly → YPoly
  | [], _ => []
  | a :: p, q => padd (pscale a q) (yshift (pmul p q))

def pevalOne : YPoly → Int
  | [] => 0
  | a :: p => a + pevalOne p

def Cpoly : Nat → YPoly
  | 0 => [2]
  | 1 => [1]
  | n + 2 => padd (Cpoly (n + 1)) (yshift (Cpoly n))

theorem C_trace_recurrence (n : Nat) :
    Cpoly (n + 2) = padd (Cpoly (n + 1)) (yshift (Cpoly n)) := by
  rfl

theorem Cpoly_one : Cpoly 1 = [1] := by
  rfl

theorem Cpoly_two : Cpoly 2 = [1, 2] := by
  rfl

theorem Cpoly_three : Cpoly 3 = [1, 3] := by
  rfl

theorem Cpoly_four : Cpoly 4 = [1, 4, 2] := by
  rfl

theorem Cpoly_five : Cpoly 5 = [1, 5, 5] := by
  rfl

theorem Cpoly_six : Cpoly 6 = [1, 6, 9, 2] := by
  rfl

theorem Cpoly_seven : Cpoly 7 = [1, 7, 14, 7] := by
  rfl

theorem Cpoly_eight : Cpoly 8 = [1, 8, 20, 16, 2] := by
  rfl

theorem Cpoly_one_at_one : pevalOne (Cpoly 1) = 1 := by
  rfl

theorem Cpoly_two_at_one : pevalOne (Cpoly 2) = 3 := by
  rfl

theorem Cpoly_three_at_one : pevalOne (Cpoly 3) = 4 := by
  rfl

theorem Cpoly_four_at_one : pevalOne (Cpoly 4) = 7 := by
  rfl

theorem Cpoly_five_at_one : pevalOne (Cpoly 5) = 11 := by
  rfl

theorem Cpoly_six_at_one : pevalOne (Cpoly 6) = 18 := by
  rfl

theorem Cpoly_seven_at_one : pevalOne (Cpoly 7) = 29 := by
  rfl

theorem Cpoly_eight_at_one : pevalOne (Cpoly 8) = 47 := by
  rfl

abbrev TPoly := List YPoly

def tadd : TPoly → TPoly → TPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => padd a b :: tadd p q

def tneg : TPoly → TPoly
  | [] => []
  | a :: p => pneg a :: tneg p

def tsub (p q : TPoly) : TPoly := tadd p (tneg q)

def tshift (p : TPoly) : TPoly := [] :: p

def tshiftN : Nat → TPoly → TPoly
  | 0, p => p
  | n + 1, p => tshift (tshiftN n p)

def tscale (a : YPoly) : TPoly → TPoly
  | [] => []
  | b :: p => pmul a b :: tscale a p

def tmul : TPoly → TPoly → TPoly
  | [], _ => []
  | a :: p, q => tadd (tscale a q) (tshift (tmul p q))

def zetaDenTy : TPoly := [[1], [-1, 0], [0, -1]]

def S6 : TPoly :=
  [Cpoly 1, Cpoly 2, Cpoly 3, Cpoly 4, Cpoly 5, Cpoly 6]

def ruelleN6Rhs : TPoly :=
  [[1], [0, 2], [0, 0, 0], [0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0],
    [-1, -7, -14, -7, 0], pneg (yshift (Cpoly 6))]

theorem ruelle_zeta_finite_certificate_N6 :
    tmul zetaDenTy S6 = ruelleN6Rhs := by
  rfl

def intAdd : List Int → List Int → List Int
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: intAdd p q

def intShift (p : List Int) : List Int := 0 :: p

def intScale (a : Int) : List Int → List Int
  | [] => []
  | b :: p => (a * b) :: intScale a p

def intPolyMul : List Int → List Int → List Int
  | [], _ => []
  | a :: p, q => intAdd (intScale a q) (intShift (intPolyMul p q))

theorem ruelle_zeta_certificate_y1_N6 :
    intPolyMul [1, -1, -1] [1, 3, 4, 7, 11, 18] =
      [1, 2, 0, 0, 0, 0, -29, -18] := by
  rfl

structure Mat2 where
  a00 : TPoly
  a01 : TPoly
  a10 : TPoly
  a11 : TPoly

def det2 (M : Mat2) : TPoly :=
  tsub (tmul M.a00 M.a11) (tmul M.a01 M.a10)

def IMinus_tTy : Mat2 :=
  Mat2.mk [[1], [-1]] [[], [0, -1]] [[], [-1]] [[1]]

theorem det_I_minus_tT : det2 IMinus_tTy = zetaDenTy := by
  rfl

abbrev Zphi := Window6GoldenPentagonRPLink.Zphi

def zzero : Zphi := Window6GoldenPentagonRPLink.zzero

def zone : Zphi := Window6GoldenPentagonRPLink.zone

def phi : Zphi := Window6GoldenPentagonRPLink.phi

def zadd (x y : Zphi) : Zphi := Window6GoldenPentagonRPLink.zadd x y

def zsub (x y : Zphi) : Zphi := Window6GoldenPentagonRPLink.zsub x y

def zmul (x y : Zphi) : Zphi := Window6GoldenPentagonRPLink.zmul x y

def zmk (a b : Int) : Zphi := Window6GoldenPentagonRPLink.Zphi.mk a b

def zneg (x : Zphi) : Zphi := zmk (-x.a) (-x.b)

def omega : Zphi := zsub phi zone

def oneMinusPhi : Zphi := zsub zone phi

def zpolyAdd : List Zphi → List Zphi → List Zphi
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => zadd a b :: zpolyAdd p q

def zpolyShift (p : List Zphi) : List Zphi := zzero :: p

def zpolyScale (a : Zphi) : List Zphi → List Zphi
  | [] => []
  | b :: p => zmul a b :: zpolyScale a p

def zpolyMul : List Zphi → List Zphi → List Zphi
  | [], _ => []
  | a :: p, q => zpolyAdd (zpolyScale a q) (zpolyShift (zpolyMul p q))

def oneMinusPhiT : List Zphi := [zone, zneg phi]

def onePlusOmegaT : List Zphi := [zone, omega]

def oneMinusTMinusT2 : List Zphi :=
  [zone, zmk (-1) 0, zmk (-1) 0]

theorem golden_pole_factorization :
    zpolyMul oneMinusPhiT onePlusOmegaT = oneMinusTMinusT2 := by
  rfl

def transferCharacteristicAt (x : Zphi) : Zphi :=
  zsub (zsub (zmul x x) x) zone

def zetaDenAt (t : Zphi) : Zphi :=
  zsub (zsub zone t) (zmul t t)

theorem transfer_spectrum :
    transferCharacteristicAt phi = zzero ∧
      transferCharacteristicAt oneMinusPhi = zzero := by
  exact And.intro rfl rfl

theorem zeta_pole_roots :
    zetaDenAt omega = zzero ∧
      zetaDenAt (zneg phi) = zzero := by
  exact And.intro rfl rfl

end BEDC.Derived.Window6GoldenMeanRuelleZeta
