import BEDC.Derived.Window6GoldenMeanRuelleZeta

namespace BEDC.Derived.Window6GoldenMeanCyclotomicPentagon

/-!
Golden-mean zeta denominator: fifth-cyclotomic twisted norm and
pentagon Gram certificate.

The file records finite identities in `Z[zeta5]`, with
`zeta5^4 = -1 - zeta5 - zeta5^2 - zeta5^3`.  The denominator
`1 - t - t^2` is connected to the real pentagon element
`u = zeta5 + zeta5^{-1}` by `u^2 + u - 1 = 0`, the four primitive
twists multiply to the integer polynomial `Q5(t,1)`, the five twists
give the scalar fifth norm, and the pentagon Gram matrix satisfies
`G^2 = 5G`.  This is a finite cyclotomic/pentagon certificate for the
golden-mean dynamical zeta denominator, not a Riemann-Hypothesis claim.
-/

structure Zeta5 where
  a0 : Int
  a1 : Int
  a2 : Int
  a3 : Int

def zmk (a : Int) : Zeta5 := Zeta5.mk a 0 0 0

def zzero : Zeta5 := Zeta5.mk 0 0 0 0

def zone : Zeta5 := Zeta5.mk 1 0 0 0

def zeta : Zeta5 := Zeta5.mk 0 1 0 0

def zadd (x y : Zeta5) : Zeta5 :=
  Zeta5.mk (x.a0 + y.a0) (x.a1 + y.a1) (x.a2 + y.a2) (x.a3 + y.a3)

def zneg (x : Zeta5) : Zeta5 :=
  Zeta5.mk (-x.a0) (-x.a1) (-x.a2) (-x.a3)

def zsub (x y : Zeta5) : Zeta5 := zadd x (zneg y)

def zmul (x y : Zeta5) : Zeta5 :=
  let c0 := x.a0 * y.a0
  let c1 := x.a0 * y.a1 + x.a1 * y.a0
  let c2 := x.a0 * y.a2 + x.a1 * y.a1 + x.a2 * y.a0
  let c3 := x.a0 * y.a3 + x.a1 * y.a2 + x.a2 * y.a1 + x.a3 * y.a0
  let c4 := x.a1 * y.a3 + x.a2 * y.a2 + x.a3 * y.a1
  let c5 := x.a2 * y.a3 + x.a3 * y.a2
  let c6 := x.a3 * y.a3
  Zeta5.mk (c0 - c4 + c5) (c1 - c4 + c6) (c2 - c4) (c3 - c4)

def zscale (n : Int) (x : Zeta5) : Zeta5 :=
  Zeta5.mk (n * x.a0) (n * x.a1) (n * x.a2) (n * x.a3)

def zpow (x : Zeta5) : Nat → Zeta5
  | 0 => zone
  | n + 1 => zmul x (zpow x n)

theorem zeta_mul_zeta_four : zmul zeta (zpow zeta 4) = zone := by
  rfl

theorem zeta_pow_five : zpow zeta 5 = zone := by
  rfl

def u : Zeta5 := zadd zeta (zpow zeta 4)

def v : Zeta5 := zneg (zadd zone u)

theorem u_min_poly : zadd (zadd (zmul u u) u) (zneg zone) = zzero := by
  rfl

theorem u_alt : zsub zone (zadd (zmul u u) u) = zzero := by
  rfl

abbrev ZPoly := List Zeta5

def zpadd : ZPoly → ZPoly → ZPoly
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => zadd a b :: zpadd p q

def zpneg : ZPoly → ZPoly
  | [] => []
  | a :: p => zneg a :: zpneg p

def zpsub (p q : ZPoly) : ZPoly := zpadd p (zpneg q)

def zpshift (p : ZPoly) : ZPoly := zzero :: p

def zpscale (a : Zeta5) : ZPoly → ZPoly
  | [] => []
  | b :: p => zmul a b :: zpscale a p

def zpmul : ZPoly → ZPoly → ZPoly
  | [], _ => []
  | a :: p, q => zpadd (zpscale a q) (zpshift (zpmul p q))

def Dk (k : Nat) : ZPoly :=
  [zone, zneg (zpow zeta k), zneg (zpow zeta (2 * k))]

def Q5at1 : ZPoly :=
  [zmk 1, zmk 1, zmk 2, zmk 3, zmk 5, zmk (-3), zmk 2, zmk (-1), zmk 1]

theorem cyclotomic_twisted_norm_primitive :
    zpmul (Dk 1) (zpmul (Dk 2) (zpmul (Dk 3) (Dk 4))) = Q5at1 := by
  rfl

def fullNorm5 : ZPoly :=
  [zmk 1, zmk 0, zmk 0, zmk 0, zmk 0, zmk (-11),
    zmk 0, zmk 0, zmk 0, zmk 0, zmk (-1)]

theorem cyclotomic_twisted_norm_full :
    zpmul (Dk 0) (zpmul (Dk 1) (zpmul (Dk 2) (zpmul (Dk 3) (Dk 4)))) =
      fullNorm5 := by
  rfl

abbrev YPoly := Window6GoldenMeanRuelleZeta.YPoly

abbrev TPoly := Window6GoldenMeanRuelleZeta.TPoly

def tpmul (p q : TPoly) : TPoly := Window6GoldenMeanRuelleZeta.tmul p q

def Q5biv : TPoly :=
  [[1], [1], [1, 1], [1, 2], [1, 3, 1],
    [0, -1, -2], [0, 0, 1, 1], [0, 0, 0, -1], [0, 0, 0, 0, 1]]

def zetaDenBiv : TPoly := [[1], [-1], [0, -1]]

def fullNormBiv : TPoly :=
  [[1], [0], [0, 0], [0, 0], [0, 0, 0], [-1, -5, -5],
    [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, -1]]

theorem scalar_cyclotomic_norm :
    tpmul zetaDenBiv Q5biv = fullNormBiv := by
  rfl

def ztwo : Zeta5 := zmk 2

def Grow : List Zeta5 := [ztwo, u, v, v, u]

def Gmat : List (List Zeta5) :=
  [[ztwo, u, v, v, u],
    [u, ztwo, u, v, v],
    [v, u, ztwo, u, v],
    [v, v, u, ztwo, u],
    [u, v, v, u, ztwo]]

def zdot : List Zeta5 → List Zeta5 → Zeta5
  | [], _ => zzero
  | _, [] => zzero
  | a :: p, b :: q => zadd (zmul a b) (zdot p q)

def znth : List Zeta5 → Nat → Zeta5
  | [], _ => zzero
  | a :: _, 0 => a
  | _ :: p, n + 1 => znth p n

def zrowAt : List (List Zeta5) → Nat → List Zeta5
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, n + 1 => zrowAt rs n

def zcolAt : List (List Zeta5) → Nat → List Zeta5
  | [], _ => []
  | r :: rs, j => znth r j :: zcolAt rs j

def zentry (A B : List (List Zeta5)) (i j : Nat) : Zeta5 :=
  zdot (zrowAt A i) (zcolAt B j)

def zmatRow (A B : List (List Zeta5)) (i : Nat) : List Zeta5 :=
  [zentry A B i 0, zentry A B i 1, zentry A B i 2, zentry A B i 3,
    zentry A B i 4]

def zmatmul (A B : List (List Zeta5)) : List (List Zeta5) :=
  [zmatRow A B 0, zmatRow A B 1, zmatRow A B 2, zmatRow A B 3, zmatRow A B 4]

def zrowscale (n : Int) : List Zeta5 → List Zeta5
  | [] => []
  | a :: r => zscale n a :: zrowscale n r

def zsmatscale (n : Int) : List (List Zeta5) → List (List Zeta5)
  | [] => []
  | r :: rs => zrowscale n r :: zsmatscale n rs

theorem pentagon_gram_idempotent :
    zmatmul Gmat Gmat = zsmatscale 5 Gmat := by
  rfl

def onePlusU : Zeta5 := zadd zone u

theorem golden_denominator_cyclotomic_factor :
    zpmul [zone, zneg onePlusU] [zone, u] = [zone, zneg zone, zneg zone] := by
  rfl

theorem golden_mean_cyclotomic_pentagon_certificate :
    zadd (zadd (zmul u u) u) (zneg zone) = zzero ∧
      zpmul (Dk 1) (zpmul (Dk 2) (zpmul (Dk 3) (Dk 4))) = Q5at1 ∧
      zpmul (Dk 0) (zpmul (Dk 1) (zpmul (Dk 2) (zpmul (Dk 3) (Dk 4)))) =
        fullNorm5 ∧
      tpmul zetaDenBiv Q5biv = fullNormBiv ∧
      zmatmul Gmat Gmat = zsmatscale 5 Gmat ∧
      zpmul [zone, zneg onePlusU] [zone, u] = [zone, zneg zone, zneg zone] := by
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl
        (And.intro rfl
          (And.intro rfl rfl))))

end BEDC.Derived.Window6GoldenMeanCyclotomicPentagon
