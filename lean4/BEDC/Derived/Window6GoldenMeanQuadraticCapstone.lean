import BEDC.Derived.Window6GoldenMeanRuelleZeta

namespace BEDC.Derived.Window6GoldenMeanQuadraticCapstone

/-!
Golden-mean zeta capstone for the quadratic algebra
`Q_y = Z[y][x] / (x^2 - x - y)`.

The master norm identity is
`(1 - t*x) * (1 + t*(x - 1)) = 1 - t - y*t^2`, and the matrix `T_y`
is the regular representation of `x`.  This honestly organizes the
determinant and Hankel-discriminant facets, most of the Parry cylinder
facet, part of the primitive-orbit and cyclotomic facets, and leaves the
strong-shift-equivalence presentation data independent.  It is not an RH
proof and not a grand unification of all golden-mean facets.
-/

abbrev YPoly := Window6GoldenMeanRuelleZeta.YPoly

abbrev TPoly := Window6GoldenMeanRuelleZeta.TPoly

def padd : YPoly → YPoly → YPoly :=
  Window6GoldenMeanRuelleZeta.padd

def pneg : YPoly → YPoly :=
  Window6GoldenMeanRuelleZeta.pneg

def yshift : YPoly → YPoly :=
  Window6GoldenMeanRuelleZeta.yshift

def tadd : TPoly → TPoly → TPoly :=
  Window6GoldenMeanRuelleZeta.tadd

def tneg : TPoly → TPoly :=
  Window6GoldenMeanRuelleZeta.tneg

def tsub (p q : TPoly) : TPoly :=
  Window6GoldenMeanRuelleZeta.tsub p q

def tshift : TPoly → TPoly :=
  Window6GoldenMeanRuelleZeta.tshift

def tmul : TPoly → TPoly → TPoly :=
  Window6GoldenMeanRuelleZeta.tmul

def zetaDenTy : TPoly :=
  Window6GoldenMeanRuelleZeta.zetaDenTy

def yElt : TPoly := [[0, 1]]

def tElt : TPoly := [[], [1]]

def Dyt : TPoly := [[1, 0], [-1, 0], [0, -1]]

def DiscY : TPoly := [[1, 4]]

def tpow (p : TPoly) : Nat → TPoly
  | 0 => [[1]]
  | n + 1 => tmul (tpow p n) p

structure Quad where
  a : TPoly
  b : TPoly

def qadd (u v : Quad) : Quad :=
  Quad.mk (tadd u.a v.a) (tadd u.b v.b)

def qneg (u : Quad) : Quad :=
  Quad.mk (tneg u.a) (tneg u.b)

def qsub (u v : Quad) : Quad :=
  qadd u (qneg v)

def tempty : TPoly → Bool
  | [] => true
  | _ :: _ => false

def tzeroShape : TPoly → TPoly
  | [] => []
  | _ :: p => [0] :: tzeroShape p

def qsmul (s : TPoly) (u : Quad) : Quad :=
  Quad.mk (if tempty u.a then tzeroShape s else tmul s u.a) (tmul s u.b)

def qmul (u v : Quad) : Quad :=
  Quad.mk
    (tadd (tadd (tmul u.a v.a) (tmul u.a v.b)) (tmul u.b v.a))
    (tadd (tmul yElt (tmul u.a v.a)) (tmul u.b v.b))

def qone : Quad := Quad.mk [] [[1]]

def qX : Quad := Quad.mk [[1]] []

def qbar (u : Quad) : Quad :=
  Quad.mk (tneg u.a) (tadd u.a u.b)

def qtrace (u : Quad) : TPoly :=
  tadd u.a (tadd u.b u.b)

def qnorm (u : Quad) : TPoly :=
  tsub (tadd (tmul u.b u.b) (tmul u.a u.b))
    (tmul yElt (tmul u.a u.a))

theorem qX_sq :
    qmul qX qX = qadd qX (qsmul yElt qone) := by
  rfl

theorem qbar_X :
    qbar qX = qsub qone qX := by
  rfl

theorem qnorm_X :
    qnorm qX = tneg yElt := by
  rfl

theorem qtrace_X :
    qtrace qX = [[1]] := by
  rfl

theorem master_norm :
    qmul (qsub qone (qsmul tElt qX))
        (qadd qone (qsmul tElt (qsub qX qone))) =
      qsmul Dyt qone := by
  rfl

structure M2 where
  a : TPoly
  b : TPoly
  c : TPoly
  d : TPoly

def mmul (M N : M2) : M2 :=
  M2.mk
    (tadd (tmul M.a N.a) (tmul M.b N.c))
    (tadd (tmul M.a N.b) (tmul M.b N.d))
    (tadd (tmul M.c N.a) (tmul M.d N.c))
    (tadd (tmul M.c N.b) (tmul M.d N.d))

def mtrace (M : M2) : TPoly :=
  tadd M.a M.d

def mdet (M : M2) : TPoly :=
  tsub (tmul M.a M.d) (tmul M.b M.c)

def rho (u : Quad) : M2 :=
  M2.mk (tadd u.a u.b) (tmul yElt u.a) u.a u.b

def TyM : M2 := M2.mk [[1]] [[0, 1]] [[1]] []

theorem rho_X :
    rho qX = TyM := by
  rfl

theorem rho_det_X :
    mdet (rho qX) = qnorm qX := by
  rfl

theorem rho_trace_X :
    mtrace (rho qX) = qtrace qX := by
  rfl

theorem rho_mul_X_X :
    rho (qmul qX qX) = mmul (rho qX) (rho qX) := by
  rfl

def FpolyY : Nat → YPoly
  | 0 => []
  | 1 => [1]
  | n + 2 => padd (FpolyY (n + 1)) (yshift (FpolyY n))

def Fpoly : Nat → TPoly
  | 0 => []
  | n + 1 => [FpolyY (n + 1)]

def qpow (u : Quad) : Nat → Quad
  | 0 => qone
  | n + 1 => qmul (qpow u n) u

def Cval (n : Nat) : TPoly :=
  qtrace (qpow qX n)

theorem pow_fib_one :
    qpow qX (1 + 1) =
      qadd (qsmul (Fpoly (1 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 1)) qone) := by
  rfl

theorem pow_fib_two :
    qpow qX (2 + 1) =
      qadd (qsmul (Fpoly (2 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 2)) qone) := by
  rfl

theorem pow_fib_three :
    qpow qX (3 + 1) =
      qadd (qsmul (Fpoly (3 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 3)) qone) := by
  rfl

theorem pow_fib_four :
    qpow qX (4 + 1) =
      qadd (qsmul (Fpoly (4 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 4)) qone) := by
  rfl

theorem pow_fib_five :
    qpow qX (5 + 1) =
      qadd (qsmul (Fpoly (5 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 5)) qone) := by
  rfl

theorem pow_fib_six :
    qpow qX (6 + 1) =
      qadd (qsmul (Fpoly (6 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 6)) qone) := by
  rfl

theorem x_pow_three_value :
    qpow qX 3 = Quad.mk [[1, 1]] [[0, 1]] := by
  rfl

theorem x_pow_four_value :
    qpow qX 4 = Quad.mk [[1, 2]] [[0, 1, 1]] := by
  rfl

theorem x_pow_five_value :
    qpow qX 5 = Quad.mk [[1, 3, 1]] [[0, 1, 2]] := by
  rfl

theorem hankel_one :
    tsub (tmul (Cval 1) (Cval (1 + 2)))
        (tmul (Cval (1 + 1)) (Cval (1 + 1))) =
      tmul (tpow (tneg yElt) 1) DiscY := by
  rfl

theorem hankel_two :
    tsub (tmul (Cval 2) (Cval (2 + 2)))
        (tmul (Cval (2 + 1)) (Cval (2 + 1))) =
      tmul (tpow (tneg yElt) 2) DiscY := by
  rfl

theorem hankel_three :
    tsub (tmul (Cval 3) (Cval (3 + 2)))
        (tmul (Cval (3 + 1)) (Cval (3 + 1))) =
      tmul (tpow (tneg yElt) 3) DiscY := by
  rfl

theorem hankel_four :
    tsub (tmul (Cval 4) (Cval (4 + 2)))
        (tmul (Cval (4 + 1)) (Cval (4 + 1))) =
      tmul (tpow (tneg yElt) 4) DiscY := by
  rfl

theorem hankel_five :
    tsub (tmul (Cval 5) (Cval (5 + 2)))
        (tmul (Cval (5 + 1)) (Cval (5 + 1))) =
      tmul (tpow (tneg yElt) 5) DiscY := by
  rfl

theorem hankel_six :
    tsub (tmul (Cval 6) (Cval (6 + 2)))
        (tmul (Cval (6 + 1)) (Cval (6 + 1))) =
      tmul (tpow (tneg yElt) 6) DiscY := by
  rfl

def qgeom : Nat → Quad
  | 0 => qone
  | n + 1 => qadd (qgeom n)
      (qsmul (tpow tElt (n + 1)) (qpow qX (n + 1)))

def resolventRhs (N : Nat) : Quad :=
  qsub
    (qsub (qadd qone (qsmul tElt (qsub qX qone)))
      (qsmul (tpow tElt (N + 1)) (qpow qX (N + 1))))
    (qsmul (tmul yElt (tpow tElt (N + 2))) (qpow qX N))

def resolventLhsOne : Quad :=
  Quad.mk [[0, 0], [1, 0], [-1, 0], [0, -1]]
    [[1, 0], [-1, 0], [0, -1], [0, 0]]

def resolventLhsTwo : Quad :=
  Quad.mk [[0, 0], [1, 0], [0, 0], [-1, -1], [0, -1]]
    [[1, 0, 0], [-1, 0, 0], [0, 0, 0], [0, -1, 0], [0, 0, -1]]

def resolventRhsOne : Quad :=
  Quad.mk [[0, 0], [1, 0], [-1, 0], [0, -1]]
    [[1, 0], [-1, 0], [0, -1], [0, 0]]

def resolventRhsTwo : Quad :=
  Quad.mk [[0, 0], [1, 0], [0, 0], [-1, -1], [0, -1]]
    [[1, 0, 0], [-1, 0, 0], [0, 0, 0], [0, -1, 0], [0, 0, -1]]

theorem master_resolvent_trunc_one :
    qsmul Dyt (qgeom 1) = resolventLhsOne := by
  rfl

theorem master_resolvent_trunc_two :
    qsmul Dyt (qgeom 2) = resolventLhsTwo := by
  rfl

theorem master_resolvent_formula_one :
    resolventRhs 1 = resolventRhsOne := by
  rfl

theorem master_resolvent_formula_two :
    resolventRhs 2 = resolventRhsTwo := by
  rfl

structure GoldenQuadCapstone where
  qX_sq_cert :
    qmul qX qX = qadd qX (qsmul yElt qone)
  qbar_X_cert :
    qbar qX = qsub qone qX
  qnorm_X_cert :
    qnorm qX = tneg yElt
  qtrace_X_cert :
    qtrace qX = [[1]]
  master_norm_cert :
    qmul (qsub qone (qsmul tElt qX))
        (qadd qone (qsmul tElt (qsub qX qone))) =
      qsmul Dyt qone
  rho_X_cert :
    rho qX = TyM
  rho_det_X_cert :
    mdet (rho qX) = qnorm qX
  rho_trace_X_cert :
    mtrace (rho qX) = qtrace qX
  rho_mul_X_X_cert :
    rho (qmul qX qX) = mmul (rho qX) (rho qX)
  pow_fib_one_cert :
    qpow qX (1 + 1) =
      qadd (qsmul (Fpoly (1 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 1)) qone)
  pow_fib_two_cert :
    qpow qX (2 + 1) =
      qadd (qsmul (Fpoly (2 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 2)) qone)
  pow_fib_three_cert :
    qpow qX (3 + 1) =
      qadd (qsmul (Fpoly (3 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 3)) qone)
  pow_fib_four_cert :
    qpow qX (4 + 1) =
      qadd (qsmul (Fpoly (4 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 4)) qone)
  pow_fib_five_cert :
    qpow qX (5 + 1) =
      qadd (qsmul (Fpoly (5 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 5)) qone)
  pow_fib_six_cert :
    qpow qX (6 + 1) =
      qadd (qsmul (Fpoly (6 + 1)) qX)
        (qsmul (tmul yElt (Fpoly 6)) qone)
  hankel_one_cert :
    tsub (tmul (Cval 1) (Cval (1 + 2)))
        (tmul (Cval (1 + 1)) (Cval (1 + 1))) =
      tmul (tpow (tneg yElt) 1) DiscY
  hankel_two_cert :
    tsub (tmul (Cval 2) (Cval (2 + 2)))
        (tmul (Cval (2 + 1)) (Cval (2 + 1))) =
      tmul (tpow (tneg yElt) 2) DiscY
  hankel_three_cert :
    tsub (tmul (Cval 3) (Cval (3 + 2)))
        (tmul (Cval (3 + 1)) (Cval (3 + 1))) =
      tmul (tpow (tneg yElt) 3) DiscY
  hankel_four_cert :
    tsub (tmul (Cval 4) (Cval (4 + 2)))
        (tmul (Cval (4 + 1)) (Cval (4 + 1))) =
      tmul (tpow (tneg yElt) 4) DiscY
  hankel_five_cert :
    tsub (tmul (Cval 5) (Cval (5 + 2)))
        (tmul (Cval (5 + 1)) (Cval (5 + 1))) =
      tmul (tpow (tneg yElt) 5) DiscY
  hankel_six_cert :
    tsub (tmul (Cval 6) (Cval (6 + 2)))
        (tmul (Cval (6 + 1)) (Cval (6 + 1))) =
      tmul (tpow (tneg yElt) 6) DiscY
  master_resolvent_trunc_one_cert :
    qsmul Dyt (qgeom 1) = resolventLhsOne
  master_resolvent_trunc_two_cert :
    qsmul Dyt (qgeom 2) = resolventLhsTwo
  master_resolvent_formula_one_cert :
    resolventRhs 1 = resolventRhsOne
  master_resolvent_formula_two_cert :
    resolventRhs 2 = resolventRhsTwo

def goldenQuadCapstone : GoldenQuadCapstone where
  qX_sq_cert := qX_sq
  qbar_X_cert := qbar_X
  qnorm_X_cert := qnorm_X
  qtrace_X_cert := qtrace_X
  master_norm_cert := master_norm
  rho_X_cert := rho_X
  rho_det_X_cert := rho_det_X
  rho_trace_X_cert := rho_trace_X
  rho_mul_X_X_cert := rho_mul_X_X
  pow_fib_one_cert := pow_fib_one
  pow_fib_two_cert := pow_fib_two
  pow_fib_three_cert := pow_fib_three
  pow_fib_four_cert := pow_fib_four
  pow_fib_five_cert := pow_fib_five
  pow_fib_six_cert := pow_fib_six
  hankel_one_cert := hankel_one
  hankel_two_cert := hankel_two
  hankel_three_cert := hankel_three
  hankel_four_cert := hankel_four
  hankel_five_cert := hankel_five
  hankel_six_cert := hankel_six
  master_resolvent_trunc_one_cert := master_resolvent_trunc_one
  master_resolvent_trunc_two_cert := master_resolvent_trunc_two
  master_resolvent_formula_one_cert := master_resolvent_formula_one
  master_resolvent_formula_two_cert := master_resolvent_formula_two

theorem golden_mean_quadratic_capstone_certificate :
    Nonempty GoldenQuadCapstone := by
  exact ⟨goldenQuadCapstone⟩

end BEDC.Derived.Window6GoldenMeanQuadraticCapstone
