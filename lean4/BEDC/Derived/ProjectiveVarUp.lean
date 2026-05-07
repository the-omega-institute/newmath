import BEDC.Derived.AffineVarUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.AffineVarUp
open BEDC.Derived.PolynomialUp

def ProjectiveVarVisibleCarrier [AskSetup] [PackageSetup] (AffPoint : BHist -> Prop)
    (PolyEvalZero : BHist -> BHist -> Prop) (family : ProbeBundle BHist)
    (tokenBundle : ProbeBundle ProbeName) (chart homogeneous projective zeroEval endpoint : BHist)
    (pkg : Pkg) : Prop :=
  AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero family chart ∧
    PolynomialSingletonCarrier homogeneous ∧
      UnaryHistory projective ∧
        Cont chart homogeneous endpoint ∧ hsame endpoint zeroEval ∧
          PkgSig tokenBundle endpoint pkg

theorem ProjectiveVarCarrier_obligation [AskSetup] [PackageSetup]
    {AffPoint : BHist -> Prop} {PolyEvalZero : BHist -> BHist -> Prop}
    {family : ProbeBundle BHist} {tokenBundle : ProbeBundle ProbeName}
    {chart homogeneous projective zeroEval endpoint endpoint' : BHist} {pkg : Pkg} :
    ProjectiveVarVisibleCarrier AffPoint PolyEvalZero family tokenBundle chart homogeneous
        projective zeroEval endpoint pkg ->
      hsame endpoint endpoint' ->
        AffineFiniteFamilyZeroLocus AffPoint PolyEvalZero family chart ∧
          PolynomialSingletonCarrier homogeneous ∧
            UnaryHistory projective ∧
              Cont chart homogeneous endpoint' ∧ hsame endpoint' zeroEval ∧
                PkgSig tokenBundle endpoint pkg := by
  intro carrier sameEndpoint
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro
          (cont_result_hsame_transport carrier.right.right.right.left sameEndpoint)
          (And.intro
            (hsame_trans (hsame_symm sameEndpoint) carrier.right.right.right.right.left)
            carrier.right.right.right.right.right))))

end BEDC.Derived.ProjectiveVarUp
