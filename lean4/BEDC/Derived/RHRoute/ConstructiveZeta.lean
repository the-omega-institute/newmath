import BEDC.Derived.RationalUp

namespace BEDC.Derived.RHRoute.ConstructiveZeta

open BEDC.FKernel.Mark
open BEDC.Derived.RationalUp

abbrev Rat := RatNum

structure RatComplex where
  re : Rat
  im : Rat

def ratSub (x y : Rat) : Rat :=
  ratAdd x (ratNeg y)

def ratComplexZero : RatComplex :=
  { re := ratZero, im := ratZero }

def ratComplexOne : RatComplex :=
  { re := ratOne, im := ratZero }

def ratComplexAdd (z w : RatComplex) : RatComplex :=
  { re := ratAdd z.re w.re, im := ratAdd z.im w.im }

def ratComplexNeg (z : RatComplex) : RatComplex :=
  { re := ratNeg z.re, im := ratNeg z.im }

def ratComplexSub (z w : RatComplex) : RatComplex :=
  ratComplexAdd z (ratComplexNeg w)

def ratComplexMul (z w : RatComplex) : RatComplex :=
  { re := ratSub (ratMul z.re w.re) (ratMul z.im w.im)
    im := ratAdd (ratMul z.re w.im) (ratMul z.im w.re) }

def ratComplexConj (z : RatComplex) : RatComplex :=
  { re := z.re, im := ratNeg z.im }

def ratComplexScale (a : Rat) (z : RatComplex) : RatComplex :=
  { re := ratMul a z.re, im := ratMul a z.im }

def ratComplexNormSq (z : RatComplex) : Rat :=
  ratAdd (ratMul z.re z.re) (ratMul z.im z.im)

def ratComplexInvApart (z : RatComplex)
    (hz : ratApart0 (ratComplexNormSq z)) : RatComplex :=
  ratComplexScale (ratInvApart (ratComplexNormSq z) hz) (ratComplexConj z)

def ratComplexDivApart (z w : RatComplex)
    (hw : ratApart0 (ratComplexNormSq w)) : RatComplex :=
  ratComplexMul z (ratComplexInvApart w hw)

def ratComplexListSum : List RatComplex -> RatComplex
  | [] => ratComplexZero
  | z :: zs => ratComplexAdd z (ratComplexListSum zs)

def RatComplexEq (z w : RatComplex) : Prop :=
  RatEq z.re w.re ∧ RatEq z.im w.im

theorem RatComplexEq_refl (z : RatComplex) : RatComplexEq z z := by
  exact And.intro (RatEq_refl z.re) (RatEq_refl z.im)

def RatStrictPositive (q : Rat) : Prop :=
  q.num.sign = BMark.b0 ∧ ratApart0 q

structure RationalStripPoint where
  re : Rat
  im : Rat
  re_positive : RatStrictPositive re
  pole_apart :
    ratApart0 (ratComplexNormSq (ratComplexSub { re := re, im := im } ratComplexOne))

structure RatBall where
  center : Rat
  diameterExp : Nat

structure ComplexBall where
  center : RatComplex
  diameterExp : Nat

def ComplexBallDiameterAtMost (ball : ComplexBall) (k : Nat) : Prop :=
  k ≤ ball.diameterExp

structure LocatedReal where
  approximate : Nat -> RatBall

structure LocatedComplex where
  approximate : Nat -> ComplexBall

structure LocatedExpLogKernel (_s : RationalStripPoint) where
  logNat : Nat -> LocatedReal
  expNegSLogNat : Nat -> LocatedComplex

def locatedNegativePower {s : RationalStripPoint}
    (kernel : LocatedExpLogKernel s) (n precision : Nat) : ComplexBall :=
  (kernel.expNegSLogNat n).approximate precision

def etaSignPositive : Nat -> Bool
  | 0 => true
  | Nat.succ 0 => false
  | Nat.succ (Nat.succ n) => etaSignPositive n

def etaSignedTerm (index : Nat) (z : RatComplex) : RatComplex :=
  match etaSignPositive index with
  | true => z
  | false => ratComplexNeg z

def etaTermApprox {s : RationalStripPoint}
    (kernel : LocatedExpLogKernel s) (index precision : Nat) : RatComplex :=
  etaSignedTerm index (locatedNegativePower kernel (Nat.succ index) precision).center

def etaTermList {s : RationalStripPoint}
    (kernel : LocatedExpLogKernel s) (N precision : Nat) : List RatComplex :=
  List.map (fun index : Nat => etaTermApprox kernel index precision) (List.range N)

def etaPartialSum {s : RationalStripPoint}
    (kernel : LocatedExpLogKernel s) (N precision : Nat) : RatComplex :=
  ratComplexListSum (etaTermList kernel N precision)

theorem etaPartialSum_eq_listSum {s : RationalStripPoint}
    (kernel : LocatedExpLogKernel s) (N precision : Nat) :
    etaPartialSum kernel N precision =
      ratComplexListSum (etaTermList kernel N precision) := by
  rfl

inductive EtaTailMethod where
  | alternating
  | dirichlet
  | eulerMaclaurin

structure EtaTailWitness (_s : RationalStripPoint)
    (targetPrecision cutoff workingPrecision : Nat) where
  method : EtaTailMethod
  dirichletBlockBudget : Nat
  eulerMaclaurinOrder : Nat
  tailDiameterExp : Nat
  cutoff_positive : 0 < cutoff
  working_covers_target : targetPrecision ≤ workingPrecision
  tail_covers_target : targetPrecision ≤ tailDiameterExp

structure EtaDenominatorData (_s : RationalStripPoint) where
  twoPowerOneMinusS : RatComplex
  denominator_apart :
    ratApart0 (ratComplexNormSq (ratComplexSub ratComplexOne twoPowerOneMinusS))
  lowerBound : Rat
  lowerBound_positive : RatStrictPositive lowerBound

def etaDenominator {s : RationalStripPoint} (data : EtaDenominatorData s) :
    RatComplex :=
  ratComplexSub ratComplexOne data.twoPowerOneMinusS

structure ZetaDivisionWitness (_s : RationalStripPoint) (targetPrecision : Nat) where
  outputDiameterExp : Nat
  output_covers_target : targetPrecision ≤ outputDiameterExp

structure ConstructiveZetaEvaluator (s : RationalStripPoint) where
  kernel : LocatedExpLogKernel s
  cutoff : Nat -> Nat
  workingPrecision : Nat -> Nat
  tailBound :
    (k : Nat) -> EtaTailWitness s k (cutoff k) (workingPrecision k)
  divisionBound : (k : Nat) -> ZetaDivisionWitness s k
  denominator : EtaDenominatorData s

def etaTailBound {s : RationalStripPoint}
    (E : ConstructiveZetaEvaluator s) (k : Nat) :
    EtaTailWitness s k (E.cutoff k) (E.workingPrecision k) :=
  E.tailBound k

theorem etaTailBound_precision {s : RationalStripPoint}
    (E : ConstructiveZetaEvaluator s) (k : Nat) :
    k ≤ (etaTailBound E k).tailDiameterExp := by
  exact (etaTailBound E k).tail_covers_target

theorem etaTailBound_working_precision {s : RationalStripPoint}
    (E : ConstructiveZetaEvaluator s) (k : Nat) :
    k ≤ E.workingPrecision k := by
  exact (etaTailBound E k).working_covers_target

def etaBallForPrecision {s : RationalStripPoint}
    (E : ConstructiveZetaEvaluator s) (k : Nat) : ComplexBall :=
  { center := etaPartialSum E.kernel (E.cutoff k) (E.workingPrecision k)
    diameterExp := (etaTailBound E k).tailDiameterExp }

def zetaFromEta {s : RationalStripPoint}
    (denominator : EtaDenominatorData s) (etaBall : ComplexBall) (k : Nat)
    (division : ZetaDivisionWitness s k) : ComplexBall :=
  { center := ratComplexDivApart etaBall.center
      (etaDenominator denominator) denominator.denominator_apart
    diameterExp := division.outputDiameterExp }

theorem zetaFromEta_diameter {s : RationalStripPoint}
    (denominator : EtaDenominatorData s) (etaBall : ComplexBall) (k : Nat)
    (division : ZetaDivisionWitness s k) :
    ComplexBallDiameterAtMost (zetaFromEta denominator etaBall k division) k := by
  exact division.output_covers_target

structure ZetaPrecisionPacket {s : RationalStripPoint}
    (E : ConstructiveZetaEvaluator s) (k : Nat) where
  tail : EtaTailWitness s k (E.cutoff k) (E.workingPrecision k)
  etaBall : ComplexBall
  etaBall_eq :
    etaBall =
      { center := etaPartialSum E.kernel (E.cutoff k) (E.workingPrecision k)
        diameterExp := tail.tailDiameterExp }
  division : ZetaDivisionWitness s k
  zetaBall : ComplexBall
  zetaBall_eq : zetaBall = zetaFromEta E.denominator etaBall k division
  zeta_diameter : ComplexBallDiameterAtMost zetaBall k
  denominator_apart :
    ratApart0 (ratComplexNormSq (etaDenominator E.denominator))

theorem zeta_evaluable_to_precision
    (s : RationalStripPoint) (E : ConstructiveZetaEvaluator s) (k : Nat) :
    ∃ packet : ZetaPrecisionPacket E k,
      ComplexBallDiameterAtMost packet.zetaBall k := by
  let tail := etaTailBound E k
  let etaBall : ComplexBall :=
    { center := etaPartialSum E.kernel (E.cutoff k) (E.workingPrecision k)
      diameterExp := tail.tailDiameterExp }
  let division := E.divisionBound k
  let zetaBall := zetaFromEta E.denominator etaBall k division
  exact
    Exists.intro
      { tail := tail
        etaBall := etaBall
        etaBall_eq := rfl
        division := division
        zetaBall := zetaBall
        zetaBall_eq := rfl
        zeta_diameter := zetaFromEta_diameter E.denominator etaBall k division
        denominator_apart := E.denominator.denominator_apart }
      (zetaFromEta_diameter E.denominator etaBall k division)

end BEDC.Derived.RHRoute.ConstructiveZeta
