namespace BEDC.Derived.Window6GoldenPentagonRPLink

/-!
Finite anchor over the golden ring Z[phi]: the 72-degree real-half
cyclotomic element `omega = 2cos(2pi/5) = phi - 1` satisfies the
golden equation `t^2 + t - 1 = 0`; the Q3 constraint value is
`sqrt5 = 2phi - 1`; and the theta=72 RP d=1 link deficit has
`16 Delta_1 = 4phi - 1`, certified golden-positive.  This ties the
fine-constants golden spectrum to the RP self-substitution
reflection-positivity line.  It is not an RH proof.
-/

structure Zphi where
  a : Int
  b : Int

def zzero : Zphi := Zphi.mk 0 0

def zone : Zphi := Zphi.mk 1 0

def phi : Zphi := Zphi.mk 0 1

def zadd (x y : Zphi) : Zphi := Zphi.mk (x.a + y.a) (x.b + y.b)

def zsub (x y : Zphi) : Zphi := Zphi.mk (x.a - y.a) (x.b - y.b)

def zmul (x y : Zphi) : Zphi :=
  Zphi.mk (x.a * y.a + x.b * y.b) (x.a * y.b + x.b * y.a + x.b * y.b)

theorem phi_sq : zmul phi phi = zadd phi zone := by
  rfl

def omega : Zphi := zsub phi zone

theorem omega_golden_min_poly :
    zadd (zadd (zmul omega omega) omega) (Zphi.mk (-1) 0) = zzero := by
  rfl

def sqrt5 : Zphi := zsub (zmul (Zphi.mk 2 0) phi) zone

theorem q3_sqrt5_eq : zadd (zmul (Zphi.mk 2 0) omega) zone = sqrt5 := by
  rfl

theorem sqrt5_sq : zmul sqrt5 sqrt5 = Zphi.mk 5 0 := by
  rfl

structure Poly5 where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  c4 : Int

def padd5 (p q : Poly5) : Poly5 :=
  Poly5.mk (p.c0 + q.c0) (p.c1 + q.c1) (p.c2 + q.c2) (p.c3 + q.c3) (p.c4 + q.c4)

def pneg5 (p : Poly5) : Poly5 :=
  Poly5.mk (-p.c0) (-p.c1) (-p.c2) (-p.c3) (-p.c4)

def psub5 (p q : Poly5) : Poly5 := padd5 p (pneg5 q)

def pmul5 (p q : Poly5) : Poly5 :=
  Poly5.mk
    (p.c0 * q.c0)
    (p.c0 * q.c1 + p.c1 * q.c0)
    (p.c0 * q.c2 + p.c1 * q.c1 + p.c2 * q.c0)
    (p.c0 * q.c3 + p.c1 * q.c2 + p.c2 * q.c1 + p.c3 * q.c0)
    (p.c0 * q.c4 + p.c1 * q.c3 + p.c2 * q.c2 + p.c3 * q.c1 + p.c4 * q.c0)

def pone5 : Poly5 := Poly5.mk 1 0 0 0 0

def px5 : Poly5 := Poly5.mk 0 1 0 0 0

def px2 : Poly5 := pmul5 px5 px5

def px3 : Poly5 := pmul5 px5 px2

def px4 : Poly5 := pmul5 px5 px3

def phi5Y : Poly5 := padd5 px2 pone5

def phi5LeftPoly : Poly5 :=
  padd5 (padd5 (padd5 (padd5 px4 px3) px2) px5) pone5

def phi5HomogenizedPoly : Poly5 :=
  psub5 (padd5 (pmul5 phi5Y phi5Y) (pmul5 px5 phi5Y)) px2

theorem phi5_left_poly_coeffs : phi5LeftPoly = Poly5.mk 1 1 1 1 1 := by
  rfl

theorem phi5_homogenized_poly_coeffs :
    phi5HomogenizedPoly = Poly5.mk 1 1 1 1 1 := by
  rfl

theorem phi5_golden_homogenization_poly :
    phi5LeftPoly = phi5HomogenizedPoly := by
  rfl

theorem phi5_golden_homogenization (_x : Int) :
    phi5LeftPoly = phi5HomogenizedPoly := by
  exact phi5_golden_homogenization_poly

def goldenPos (z : Zphi) : Prop := 0 < 2 * z.a + z.b ∧ 0 ≤ z.b

def linkDeficit16 : Zphi := zsub (zmul (Zphi.mk 4 0) phi) zone

theorem link_deficit16_coords : linkDeficit16 = Zphi.mk (-1) 4 := by
  rfl

theorem link_deficit_golden_positive : goldenPos linkDeficit16 := by
  exact And.intro (Int.NonNeg.mk 1) (Int.NonNeg.mk 4)

theorem concrete_phi_square_coords : zmul phi phi = Zphi.mk 1 1 := by
  rfl

theorem concrete_omega_coords : omega = Zphi.mk (-1) 1 := by
  rfl

theorem concrete_sqrt5_coords : sqrt5 = Zphi.mk (-1) 2 := by
  rfl

theorem concrete_link_deficit16_coords : linkDeficit16 = Zphi.mk (-1) 4 := by
  rfl

end BEDC.Derived.Window6GoldenPentagonRPLink
