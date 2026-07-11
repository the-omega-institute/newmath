import BEDC.Derived.Window6GoldenPentagonRPLink
import BEDC.Derived.Window6GoldenMeanRuelleZeta

namespace BEDC.Derived.Window6GoldenMeanParryResidue

/-!
Finite Parry/Ruelle-Perron-Frobenius certificate for the golden-mean
subshift: cylinder-resolved counts, Perron residue with exact psi-error,
and the pressure derivative C_n' = n F_{n-1}.  This is not an RH proof,
not about the Riemann xi, and not a new Euler product.
-/

abbrev YPoly := Window6GoldenMeanRuelleZeta.YPoly

abbrev padd : YPoly → YPoly → YPoly :=
  Window6GoldenMeanRuelleZeta.padd

abbrev pneg : YPoly → YPoly :=
  Window6GoldenMeanRuelleZeta.pneg

abbrev psub : YPoly → YPoly → YPoly :=
  Window6GoldenMeanRuelleZeta.psub

abbrev yshift : YPoly → YPoly :=
  Window6GoldenMeanRuelleZeta.yshift

abbrev pscale : Int → YPoly → YPoly :=
  Window6GoldenMeanRuelleZeta.pscale

abbrev pmul : YPoly → YPoly → YPoly :=
  Window6GoldenMeanRuelleZeta.pmul

def Fpoly : Nat → YPoly
  | 0 => []
  | 1 => [1]
  | n + 2 => padd (Fpoly (n + 1)) (yshift (Fpoly n))

theorem Fpoly_one : Fpoly 1 = [1] := by
  rfl

theorem Fpoly_two : Fpoly 2 = [1] := by
  rfl

theorem Fpoly_three : Fpoly 3 = [1, 1] := by
  rfl

theorem Fpoly_four : Fpoly 4 = [1, 2] := by
  rfl

theorem Fpoly_five : Fpoly 5 = [1, 3, 1] := by
  rfl

theorem Fpoly_six : Fpoly 6 = [1, 4, 3] := by
  rfl

theorem Fpoly_seven : Fpoly 7 = [1, 5, 6, 1] := by
  rfl

theorem Fpoly_eight : Fpoly 8 = [1, 6, 10, 4] := by
  rfl

structure Mat2Y where
  a : YPoly
  b : YPoly
  c : YPoly
  d : YPoly

def maddY (M N : Mat2Y) : Mat2Y :=
  Mat2Y.mk (padd M.a N.a) (padd M.b N.b) (padd M.c N.c) (padd M.d N.d)

def mmulY (M N : Mat2Y) : Mat2Y :=
  Mat2Y.mk
    (padd (pmul M.a N.a) (pmul M.b N.c))
    (padd (pmul M.a N.b) (pmul M.b N.d))
    (padd (pmul M.c N.a) (pmul M.d N.c))
    (padd (pmul M.c N.b) (pmul M.d N.d))

def IY : Mat2Y := Mat2Y.mk [1] [] [] [1]

def Ty : Mat2Y := Mat2Y.mk [1] [0, 1] [1] []

def mpowY : Nat → Mat2Y
  | 0 => IY
  | n + 1 => mmulY Ty (mpowY n)

theorem Ty_pow_cylinder_1 :
    mpowY 1 = Mat2Y.mk [1, 0] [0, 1] [1] [0] := by
  rfl

theorem Ty_pow_cylinder_2 :
    mpowY 2 = Mat2Y.mk [1, 1] [0, 1] [1, 0] [0, 1] := by
  rfl

theorem Ty_pow_cylinder_3 :
    mpowY 3 = Mat2Y.mk [1, 2, 0] [0, 1, 1] [1, 1] [0, 1] := by
  rfl

theorem Ty_pow_cylinder_4 :
    mpowY 4 = Mat2Y.mk [1, 3, 1] [0, 1, 2] [1, 2, 0] [0, 1, 1] := by
  rfl

theorem Ty_pow_cylinder_5 :
    mpowY 5 = Mat2Y.mk [1, 4, 3, 0] [0, 1, 3, 1] [1, 3, 1] [0, 1, 2] := by
  rfl

theorem Ty_pow_cylinder_6 :
    mpowY 6 = Mat2Y.mk [1, 5, 6, 1] [0, 1, 4, 3] [1, 4, 3, 0] [0, 1, 3, 1] := by
  rfl

theorem Ty_pow_cylinder_7 :
    mpowY 7 = Mat2Y.mk [1, 6, 10, 4, 0] [0, 1, 5, 6, 1] [1, 5, 6, 1] [0, 1, 4, 3] := by
  rfl

theorem Ty_pow_cylinder_8 :
    mpowY 8 = Mat2Y.mk [1, 7, 15, 10, 1] [0, 1, 6, 10, 4] [1, 6, 10, 4, 0] [0, 1, 5, 6, 1] := by
  rfl

def Ctrace (n : Nat) : YPoly :=
  padd (Fpoly (n + 1)) (yshift (Fpoly (n - 1)))

def N0 (n : Nat) : YPoly := Fpoly (n + 1)

def N1 : Nat → YPoly
  | 0 => []
  | 1 => []
  | n + 2 => yshift (Fpoly (n + 1))

theorem Ctrace_one : Ctrace 1 = [1] := by
  rfl

theorem Ctrace_two : Ctrace 2 = [1, 2] := by
  rfl

theorem Ctrace_three : Ctrace 3 = [1, 3] := by
  rfl

theorem Ctrace_four : Ctrace 4 = [1, 4, 2] := by
  rfl

theorem Ctrace_five : Ctrace 5 = [1, 5, 5] := by
  rfl

theorem Ctrace_six : Ctrace 6 = [1, 6, 9, 2] := by
  rfl

theorem Ctrace_seven : Ctrace 7 = [1, 7, 14, 7] := by
  rfl

theorem Ctrace_eight : Ctrace 8 = [1, 8, 20, 16, 2] := by
  rfl

theorem Ctrace_eq_Cpoly_1 :
    Ctrace 1 = Window6GoldenMeanRuelleZeta.Cpoly 1 := by
  rfl

theorem Ctrace_eq_Cpoly_2 :
    Ctrace 2 = Window6GoldenMeanRuelleZeta.Cpoly 2 := by
  rfl

theorem Ctrace_eq_Cpoly_3 :
    Ctrace 3 = Window6GoldenMeanRuelleZeta.Cpoly 3 := by
  rfl

theorem Ctrace_eq_Cpoly_4 :
    Ctrace 4 = Window6GoldenMeanRuelleZeta.Cpoly 4 := by
  rfl

theorem Ctrace_eq_Cpoly_5 :
    Ctrace 5 = Window6GoldenMeanRuelleZeta.Cpoly 5 := by
  rfl

theorem Ctrace_eq_Cpoly_6 :
    Ctrace 6 = Window6GoldenMeanRuelleZeta.Cpoly 6 := by
  rfl

theorem Ctrace_eq_Cpoly_7 :
    Ctrace 7 = Window6GoldenMeanRuelleZeta.Cpoly 7 := by
  rfl

theorem Ctrace_eq_Cpoly_8 :
    Ctrace 8 = Window6GoldenMeanRuelleZeta.Cpoly 8 := by
  rfl

theorem N0_one : N0 1 = [1] := by
  rfl

theorem N0_two : N0 2 = [1, 1] := by
  rfl

theorem N0_three : N0 3 = [1, 2] := by
  rfl

theorem N0_four : N0 4 = [1, 3, 1] := by
  rfl

theorem N0_five : N0 5 = [1, 4, 3] := by
  rfl

theorem N0_six : N0 6 = [1, 5, 6, 1] := by
  rfl

theorem N1_one : N1 1 = [] := by
  rfl

theorem N1_two : N1 2 = [0, 1] := by
  rfl

theorem N1_three : N1 3 = [0, 1] := by
  rfl

theorem N1_four : N1 4 = [0, 1, 1] := by
  rfl

theorem N1_five : N1 5 = [0, 1, 2] := by
  rfl

theorem N1_six : N1 6 = [0, 1, 3, 1] := by
  rfl

abbrev TPoly := Window6GoldenMeanRuelleZeta.TPoly

abbrev tadd : TPoly → TPoly → TPoly :=
  Window6GoldenMeanRuelleZeta.tadd

abbrev tneg : TPoly → TPoly :=
  Window6GoldenMeanRuelleZeta.tneg

abbrev tsub : TPoly → TPoly → TPoly :=
  Window6GoldenMeanRuelleZeta.tsub

abbrev tmul : TPoly → TPoly → TPoly :=
  Window6GoldenMeanRuelleZeta.tmul

structure Mat2T where
  a : TPoly
  b : TPoly
  c : TPoly
  d : TPoly

def mmulT (M N : Mat2T) : Mat2T :=
  Mat2T.mk
    (tadd (tmul M.a N.a) (tmul M.b N.c))
    (tadd (tmul M.a N.b) (tmul M.b N.d))
    (tadd (tmul M.c N.a) (tmul M.d N.c))
    (tadd (tmul M.c N.b) (tmul M.d N.d))

def IMinus_tTy : Mat2T :=
  Mat2T.mk [[1], [-1]] [[], [0, -1]] [[], [-1]] [[1]]

def adj_Iminus_tTy : Mat2T :=
  Mat2T.mk [[1]] [[], [0, 1]] [[], [1]] [[1], [-1]]

def zetaDenTy : TPoly := [[1], [-1], [0, -1]]

def zetaDenTyI : Mat2T :=
  Mat2T.mk [[1], [-1, 0], [0, -1]] [[0], [0, 0], [0, 0]] [[0], [0]] [[1], [-1], [0, -1]]

theorem resolvent_adjugate_identity :
    mmulT IMinus_tTy adj_Iminus_tTy = zetaDenTyI := by
  rfl

def dPolyTail : Nat → YPoly → YPoly
  | _, [] => []
  | k, a :: p => (Int.ofNat k * a) :: dPolyTail (k + 1) p

def dPoly : YPoly → YPoly
  | [] => []
  | _ :: p => dPolyTail 1 p

theorem pressure_derivative_2 :
    dPoly (Ctrace 2) = pscale (Int.ofNat 2) (Fpoly 1) := by
  rfl

theorem pressure_derivative_3 :
    dPoly (Ctrace 3) = pscale (Int.ofNat 3) (Fpoly 2) := by
  rfl

theorem pressure_derivative_4 :
    dPoly (Ctrace 4) = pscale (Int.ofNat 4) (Fpoly 3) := by
  rfl

theorem pressure_derivative_5 :
    dPoly (Ctrace 5) = pscale (Int.ofNat 5) (Fpoly 4) := by
  rfl

theorem pressure_derivative_6 :
    dPoly (Ctrace 6) = pscale (Int.ofNat 6) (Fpoly 5) := by
  rfl

theorem pressure_derivative_7 :
    dPoly (Ctrace 7) = pscale (Int.ofNat 7) (Fpoly 6) := by
  rfl

theorem pressure_derivative_8 :
    dPoly (Ctrace 8) = pscale (Int.ofNat 8) (Fpoly 7) := by
  rfl

abbrev Zphi := Window6GoldenPentagonRPLink.Zphi

def zmk (a b : Int) : Zphi := Window6GoldenPentagonRPLink.Zphi.mk a b

def zzero : Zphi := Window6GoldenPentagonRPLink.zzero

def zone : Zphi := Window6GoldenPentagonRPLink.zone

def phi : Zphi := Window6GoldenPentagonRPLink.phi

def zadd (x y : Zphi) : Zphi := Window6GoldenPentagonRPLink.zadd x y

def zsub (x y : Zphi) : Zphi := Window6GoldenPentagonRPLink.zsub x y

def zmul (x y : Zphi) : Zphi := Window6GoldenPentagonRPLink.zmul x y

def zneg (x : Zphi) : Zphi := zmk (-x.a) (-x.b)

def zint (a : Int) : Zphi := zmk a 0

def oneMinusPhi : Zphi := zsub zone phi

def psi : Zphi := oneMinusPhi

def zpow (x : Zphi) : Nat → Zphi
  | 0 => zone
  | n + 1 => zmul x (zpow x n)

def LucasZ : Nat → Zphi
  | 0 => zint 2
  | 1 => zone
  | n + 2 => zadd (LucasZ (n + 1)) (LucasZ n)

structure Mat2Z where
  a : Zphi
  b : Zphi
  c : Zphi
  d : Zphi

def zaddMat (M N : Mat2Z) : Mat2Z :=
  Mat2Z.mk (zadd M.a N.a) (zadd M.b N.b) (zadd M.c N.c) (zadd M.d N.d)

def zsubMat (M N : Mat2Z) : Mat2Z :=
  Mat2Z.mk (zsub M.a N.a) (zsub M.b N.b) (zsub M.c N.c) (zsub M.d N.d)

def zsMat (r : Zphi) (M : Mat2Z) : Mat2Z :=
  Mat2Z.mk (zmul r M.a) (zmul r M.b) (zmul r M.c) (zmul r M.d)

def mmulZ (M N : Mat2Z) : Mat2Z :=
  Mat2Z.mk
    (zadd (zmul M.a N.a) (zmul M.b N.c))
    (zadd (zmul M.a N.b) (zmul M.b N.d))
    (zadd (zmul M.c N.a) (zmul M.d N.c))
    (zadd (zmul M.c N.b) (zmul M.d N.d))

def IZ : Mat2Z := Mat2Z.mk zone zzero zzero zone

def Tgolden : Mat2Z := Mat2Z.mk zone zone zone zzero

def mpowZ : Nat → Mat2Z
  | 0 => IZ
  | n + 1 => mmulZ Tgolden (mpowZ n)

def s : Zphi := zmk (-1) 2

def P : Mat2Z := Mat2Z.mk phi zone zone (zsub phi zone)

def Q : Mat2Z := Mat2Z.mk (zsub zone phi) zone zone (zneg phi)

theorem phi_square_residue : zmul phi phi = zadd phi zone := by
  rfl

theorem golden_parry_spectral_0 :
    zsMat s (mpowZ 0) = zsubMat (zsMat (zpow phi 0) P) (zsMat (zpow psi 0) Q) := by
  rfl

theorem golden_parry_spectral_1 :
    zsMat s (mpowZ 1) = zsubMat (zsMat (zpow phi 1) P) (zsMat (zpow psi 1) Q) := by
  rfl

theorem golden_parry_spectral_2 :
    zsMat s (mpowZ 2) = zsubMat (zsMat (zpow phi 2) P) (zsMat (zpow psi 2) Q) := by
  rfl

theorem golden_parry_spectral_3 :
    zsMat s (mpowZ 3) = zsubMat (zsMat (zpow phi 3) P) (zsMat (zpow psi 3) Q) := by
  rfl

theorem golden_parry_spectral_4 :
    zsMat s (mpowZ 4) = zsubMat (zsMat (zpow phi 4) P) (zsMat (zpow psi 4) Q) := by
  rfl

theorem golden_parry_spectral_5 :
    zsMat s (mpowZ 5) = zsubMat (zsMat (zpow phi 5) P) (zsMat (zpow psi 5) Q) := by
  rfl

theorem golden_parry_spectral_6 :
    zsMat s (mpowZ 6) = zsubMat (zsMat (zpow phi 6) P) (zsMat (zpow psi 6) Q) := by
  rfl

theorem golden_parry_error_1_00 :
    zmul s (mpowZ 1).a = zsub (zmul phi (LucasZ 1)) (zpow psi 1) := by
  rfl

theorem golden_parry_error_2_00 :
    zmul s (mpowZ 2).a = zsub (zmul phi (LucasZ 2)) (zpow psi 2) := by
  rfl

theorem golden_parry_error_3_00 :
    zmul s (mpowZ 3).a = zsub (zmul phi (LucasZ 3)) (zpow psi 3) := by
  rfl

theorem golden_parry_error_4_00 :
    zmul s (mpowZ 4).a = zsub (zmul phi (LucasZ 4)) (zpow psi 4) := by
  rfl

theorem golden_parry_error_5_00 :
    zmul s (mpowZ 5).a = zsub (zmul phi (LucasZ 5)) (zpow psi 5) := by
  rfl

theorem golden_parry_error_6_00 :
    zmul s (mpowZ 6).a = zsub (zmul phi (LucasZ 6)) (zpow psi 6) := by
  rfl

theorem golden_parry_error_1_11 :
    zmul s (mpowZ 1).d = zadd (zmul (zsub phi zone) (LucasZ 1)) (zpow psi 1) := by
  rfl

theorem golden_parry_error_2_11 :
    zmul s (mpowZ 2).d = zadd (zmul (zsub phi zone) (LucasZ 2)) (zpow psi 2) := by
  rfl

theorem golden_parry_error_3_11 :
    zmul s (mpowZ 3).d = zadd (zmul (zsub phi zone) (LucasZ 3)) (zpow psi 3) := by
  rfl

theorem golden_parry_error_4_11 :
    zmul s (mpowZ 4).d = zadd (zmul (zsub phi zone) (LucasZ 4)) (zpow psi 4) := by
  rfl

theorem golden_parry_error_5_11 :
    zmul s (mpowZ 5).d = zadd (zmul (zsub phi zone) (LucasZ 5)) (zpow psi 5) := by
  rfl

theorem golden_parry_error_6_11 :
    zmul s (mpowZ 6).d = zadd (zmul (zsub phi zone) (LucasZ 6)) (zpow psi 6) := by
  rfl

theorem golden_mean_parry_residue_certificate :
    mpowY 8 = Mat2Y.mk [1, 7, 15, 10, 1] [0, 1, 6, 10, 4] [1, 6, 10, 4, 0] [0, 1, 5, 6, 1] ∧
      mmulT IMinus_tTy adj_Iminus_tTy = zetaDenTyI ∧
        dPoly (Ctrace 8) = pscale (Int.ofNat 8) (Fpoly 7) ∧
          zsMat s (mpowZ 6) = zsubMat (zsMat (zpow phi 6) P) (zsMat (zpow psi 6) Q) ∧
            zmul s (mpowZ 6).a = zsub (zmul phi (LucasZ 6)) (zpow psi 6) ∧
              zmul s (mpowZ 6).d = zadd (zmul (zsub phi zone) (LucasZ 6)) (zpow psi 6) := by
  exact
    And.intro Ty_pow_cylinder_8
      (And.intro resolvent_adjugate_identity
        (And.intro pressure_derivative_8
          (And.intro golden_parry_spectral_6
            (And.intro golden_parry_error_6_00 golden_parry_error_6_11))))

end BEDC.Derived.Window6GoldenMeanParryResidue
