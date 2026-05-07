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

def ProjectiveVarVisibleCarrier [AskSetup] [PackageSetup]
    (chart homogeneous projective evaluation endpoint : BHist) (polyBundle : ProbeBundle BHist)
    (tokenBundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory chart ∧ PolynomialSingletonCarrier homogeneous ∧ UnaryHistory projective ∧
    AffineFiniteFamilyZeroLocus UnaryHistory
      (fun p x => hsame (append p x) BHist.Empty) polyBundle chart ∧
      Cont chart homogeneous evaluation ∧ TokIntro tokenBundle evaluation pkg ∧
        Cont evaluation projective endpoint

theorem ProjectiveVarVisibleCarrier_carrier_obligation [AskSetup] [PackageSetup]
    {chart homogeneous projective evaluation endpoint : BHist} {polyBundle : ProbeBundle BHist}
    {tokenBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProjectiveVarVisibleCarrier chart homogeneous projective evaluation endpoint polyBundle
        tokenBundle pkg ->
      UnaryHistory chart ∧ PolynomialSingletonCarrier homogeneous ∧ UnaryHistory projective ∧
        AffineFiniteFamilyZeroLocus UnaryHistory
          (fun p x => hsame (append p x) BHist.Empty) polyBundle chart ∧
          Cont chart homogeneous evaluation ∧ TokIntro tokenBundle evaluation pkg ∧
            Cont evaluation projective endpoint ∧ UnaryHistory evaluation ∧
              UnaryHistory endpoint := by
  intro carrier
  have homogeneousUnary : UnaryHistory homogeneous :=
    unary_transport unary_empty (hsame_symm carrier.right.left)
  have evaluationUnary : UnaryHistory evaluation :=
    unary_cont_closed carrier.left homogeneousUnary carrier.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed evaluationUnary carrier.right.right.left
      carrier.right.right.right.right.right.right
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right
                (And.intro evaluationUnary endpointUnary)))))))

theorem ProjectiveVarVisibleCarrier_classifier_stability [AskSetup] [PackageSetup]
    {chart homogeneous projective evaluation endpoint endpoint' : BHist}
    {polyBundle : ProbeBundle BHist} {tokenBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProjectiveVarVisibleCarrier chart homogeneous projective evaluation endpoint polyBundle
        tokenBundle pkg ->
      hsame endpoint endpoint' ->
        ProjectiveVarVisibleCarrier chart homogeneous projective evaluation endpoint' polyBundle
          tokenBundle pkg := by
  intro carrier sameEndpoint
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.right.right.right.left
          (And.intro carrier.right.right.right.right.left
            (And.intro carrier.right.right.right.right.right.left
              (cont_result_hsame_transport
                carrier.right.right.right.right.right.right sameEndpoint))))))

end BEDC.Derived.ProjectiveVarUp
