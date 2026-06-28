import BEDC.Derived.RHRoute.LocatedZetaZero
import BEDC.Derived.RHRoute.ZetaBoxEvaluator

namespace BEDC.Derived.RHRoute.KrawczykCertificate

open BEDC.Derived.RationalUp

abbrev Rat : Type :=
  RatNum

abbrev RatComplex : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.RatComplex

abbrev LocatedComplex : Type :=
  BEDC.Derived.RHRoute.LocatedZetaZero.LocatedComplex

abbrev ComplexBox : Type :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ComplexBox

def ratComplexZero : RatComplex :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexZero

def ratComplexSub (z w : RatComplex) : RatComplex :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexSub z w

def ratComplexMul (z w : RatComplex) : RatComplex :=
  BEDC.Derived.RHRoute.ZetaBoxEvaluator.ratComplexMul z w

def dist (z w : RatComplex) : Rat :=
  ratAdd (ratDist z.re w.re) (ratDist z.im w.im)

structure ClosedBall where
  center : RatComplex
  radius : Rat

def Ball (c : RatComplex) (r : Rat) : ClosedBall :=
  { center := c, radius := r }

def ClosedBall.ContainsRat (B : ClosedBall) (z : RatComplex) : Prop :=
  ratLe (dist z B.center) B.radius

def ClosedBall.ContainsLocated (B : ClosedBall) (rho : LocatedComplex) : Prop :=
  ∀ n : Nat, ∀ z : RatComplex,
    (rho.R n).ContainsPoint z -> B.ContainsRat z

instance closedBallRatMembership : Membership RatComplex ClosedBall where
  mem B z := B.ContainsRat z

def LocatedInBall (rho : LocatedComplex) (c : RatComplex) (r : Rat) : Prop :=
  (Ball c r).ContainsLocated rho

structure CMap where
  evalRat : RatComplex -> RatComplex

instance cmapCoeFun : CoeFun CMap (fun _ => RatComplex -> RatComplex) where
  coe F := F.evalRat

structure CFun extends CMap

instance cfunCoeFun : CoeFun CFun (fun _ => RatComplex -> RatComplex) where
  coe F := F.evalRat

def CFun.VanishesAt (F : CFun) (rho : LocatedComplex) : Prop :=
  ∀ n : Nat, ∃ z : RatComplex,
    (rho.R n).ContainsPoint z ∧ F z = ratComplexZero

def ComplexInBox (z : RatComplex) (box : ComplexBox) : Prop :=
  BEDC.Derived.RHRoute.LocatedZetaZero.ComplexInBox z box

-- 固定点读法只用窗口流: 每个 located 窗口中有有理见证,
-- 且该见证被 Newton 映射精确固定。
def FixedPoint (N : CMap) (rho : LocatedComplex) : Prop :=
  ∀ n : Nat, ∃ z : RatComplex,
    (rho.R n).ContainsPoint z ∧ N z = z

structure BanachIterationTrace
    (c : RatComplex) (r : Rat) (N : CMap) (lambda : Rat) where
  picard : Nat -> RatComplex
  seed : picard 0 = c
  step : ∀ n : Nat, picard (Nat.succ n) = N (picard n)
  picard_in_ball : ∀ n : Nat, picard n ∈ Ball c r
  cauchy_modulus :
    ∀ k m n : Nat, k ≤ m -> k ≤ n ->
      ratLe (dist (picard m) (picard n))
        (BEDC.Derived.RHRoute.LocatedZetaZero.dyad k)
  limit : LocatedComplex
  limit_in_ball : LocatedInBall limit c r
  picard_locates : ∀ n : Nat, (limit.R n).ContainsPoint (picard n)
  image_locates : ∀ n : Nat, (limit.R n).ContainsPoint (N (picard n))
  fixed_witnesses : FixedPoint N limit

theorem BanachIterationTrace.fixed_point
    {c : RatComplex} {r : Rat} {N : CMap} {lambda : Rat}
    (trace : BanachIterationTrace c r N lambda) :
    FixedPoint N trace.limit :=
  trace.fixed_witnesses

structure ContractionZeroCert (F : CFun) where
  c : RatComplex
  r : Rat
  N : CMap
  lambda : Rat
  hr : ratLt ratZero r
  hlambda0 : ratLe ratZero lambda
  hlambda1 : ratLt lambda ratOne
  maps_ball : ∀ z : RatComplex, z ∈ Ball c r -> N z ∈ Ball c r
  contract :
    ∀ z w : RatComplex,
      z ∈ Ball c r ->
      w ∈ Ball c r ->
        ratLe (dist (N z) (N w)) (ratMul lambda (dist z w))
  fixed_implies_zero :
    ∀ z : RatComplex, z ∈ Ball c r -> N z = z -> F z = ratComplexZero
  trace : BanachIterationTrace c r N lambda

theorem located_fixed_point_of_contraction {F : CFun}
    (cert : ContractionZeroCert F) :
    ∃ rho : LocatedComplex,
      LocatedInBall rho cert.c cert.r ∧ FixedPoint cert.N rho := by
  exact
    Exists.intro cert.trace.limit
      (And.intro cert.trace.limit_in_ball cert.trace.fixed_point)

theorem located_zero_of_contraction_cert {F : CFun}
    (cert : ContractionZeroCert F) :
    ∃ rho : LocatedComplex,
      LocatedInBall rho cert.c cert.r ∧ F.VanishesAt rho := by
  cases located_fixed_point_of_contraction cert with
  | intro rho fixedData =>
      exact
        Exists.intro rho
          (And.intro fixedData.left
            (by
              intro n
              cases fixedData.right n with
              | intro z zFixed =>
                  have zInBall : z ∈ Ball cert.c cert.r :=
                    fixedData.left n z zFixed.left
                  exact
                    Exists.intro z
                      (And.intro zFixed.left
                        (cert.fixed_implies_zero z zInBall zFixed.right))))

structure ZetaAnalyticInterface where
  zeta : CFun
  zetaDerivative : CMap

def zetaNewtonMap (I : ZetaAnalyticInterface) (a : RatComplex) : CMap :=
  { evalRat := fun z => ratComplexSub z (ratComplexMul a (I.zeta z)) }

structure ZetaResidualBoxBound
    (I : ZetaAnalyticInterface) (c : RatComplex) where
  precision : Nat
  residualBox : ComplexBox
  center_sound : ComplexInBox (I.zeta c) residualBox

structure ZetaDerivativeBoxBound
    (I : ZetaAnalyticInterface) (c : RatComplex) (r : Rat) where
  precision : Nat
  derivativeBox : ComplexBox
  derivative_sound :
    ∀ z : RatComplex, z ∈ Ball c r ->
      ComplexInBox (I.zetaDerivative z) derivativeBox

structure ZetaKrawczykCert (I : ZetaAnalyticInterface) where
  c : RatComplex
  a : RatComplex
  r : Rat
  lambda : Rat
  hr : ratLt ratZero r
  hlambda0 : ratLe ratZero lambda
  hlambda1 : ratLt lambda ratOne
  residual_bound : ZetaResidualBoxBound I c
  derivative_box_bound : ZetaDerivativeBoxBound I c r
  checker_sound : ContractionZeroCert I.zeta
  checker_center : checker_sound.c = c
  checker_radius : checker_sound.r = r
  checker_ratio : checker_sound.lambda = lambda
  checker_newton_readback :
    ∀ z : RatComplex, checker_sound.N z = zetaNewtonMap I a z

theorem located_zero_of_zeta_krawczyk_cert {I : ZetaAnalyticInterface}
    (cert : ZetaKrawczykCert I) :
    ∃ rho : LocatedComplex,
      LocatedInBall rho cert.checker_sound.c cert.checker_sound.r ∧
        I.zeta.VanishesAt rho := by
  exact located_zero_of_contraction_cert cert.checker_sound

end BEDC.Derived.RHRoute.KrawczykCertificate
