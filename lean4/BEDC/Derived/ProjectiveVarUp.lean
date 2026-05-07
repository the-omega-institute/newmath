import BEDC.Derived.AffineVarUp
import BEDC.Derived.PolynomialUp
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.Derived.AffineVarUp
open BEDC.Derived.PolynomialUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ProjectiveVarCarrier
    (endpoint chart homogeneous projective zeroEval provenance : BHist) : Prop :=
  UnaryHistory endpoint ∧ UnaryHistory chart ∧ UnaryHistory homogeneous ∧
    Cont chart homogeneous projective ∧ Cont projective zeroEval endpoint ∧
      hsame provenance endpoint

theorem ProjectiveVarCarrier_chart_homogeneous_transport
    {endpoint endpoint' chart chart' homogeneous homogeneous' projective projective' zeroEval
      provenance : BHist} :
    ProjectiveVarCarrier endpoint chart homogeneous projective zeroEval provenance ->
      hsame chart chart' -> hsame homogeneous homogeneous' ->
        Cont chart' homogeneous' projective' -> Cont projective' zeroEval endpoint' ->
          ProjectiveVarCarrier endpoint' chart' homogeneous' projective' zeroEval endpoint' ∧
            hsame projective projective' ∧ hsame endpoint endpoint' := by
  intro carrier sameChart sameHomogeneous transportedProjective transportedEndpoint
  have chartUnary : UnaryHistory chart' :=
    unary_transport carrier.right.left sameChart
  have homogeneousUnary : UnaryHistory homogeneous' :=
    unary_transport carrier.right.right.left sameHomogeneous
  have projectiveSame : hsame projective projective' :=
    cont_respects_hsame sameChart sameHomogeneous carrier.right.right.right.left
      transportedProjective
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame projectiveSame (hsame_refl zeroEval)
      carrier.right.right.right.right.left transportedEndpoint
  have endpointUnary : UnaryHistory endpoint' :=
    unary_transport carrier.left endpointSame
  exact And.intro
    (And.intro endpointUnary
      (And.intro chartUnary
        (And.intro homogeneousUnary
          (And.intro transportedProjective
            (And.intro transportedEndpoint (hsame_refl endpoint'))))))
    (And.intro projectiveSame endpointSame)

def ProjectiveVarTransportCarrier [AskSetup] [PackageSetup] (AffPoint : BHist -> Prop)
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
    ProjectiveVarTransportCarrier AffPoint PolyEvalZero family tokenBundle chart homogeneous
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

end BEDC.Derived.ProjectiveVarUp
