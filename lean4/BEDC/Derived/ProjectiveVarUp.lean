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

theorem ProjectiveVarVisibleCarrier_zero_locus_exactness [AskSetup] [PackageSetup]
    {chart homogeneous projective evaluation endpoint p : BHist} {polyBundle : ProbeBundle BHist}
    {tokenBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProjectiveVarVisibleCarrier chart homogeneous projective evaluation endpoint polyBundle
        tokenBundle pkg ->
      InBundle p polyBundle ->
        hsame (append p chart) BHist.Empty ∧ Cont chart homogeneous evaluation ∧
          TokIntro tokenBundle evaluation pkg ∧ Cont evaluation projective endpoint := by
  intro carrier member
  have zeroRow : hsame (append p chart) BHist.Empty :=
    AffineFiniteFamilyZeroLocus_occurred_equation_row
      (AffPoint := UnaryHistory)
      (PolyEvalZero := fun q x => hsame (append q x) BHist.Empty)
      (F := polyBundle) (p := p) (x := chart) member carrier.right.right.right.left
  exact And.intro zeroRow
    (And.intro carrier.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.left
        carrier.right.right.right.right.right.right))

theorem ProjectiveVarVisibleCarrier_scaling_ledger [AskSetup] [PackageSetup]
    {chart homogeneous projective evaluation endpoint hiddenScale hiddenChart hiddenRoute : BHist}
    {polyBundle : ProbeBundle BHist} {tokenBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ProjectiveVarVisibleCarrier chart homogeneous projective evaluation endpoint polyBundle
        tokenBundle pkg ->
      Cont hiddenScale hiddenChart hiddenRoute ->
        hsame hiddenRoute BHist.Empty ->
          hsame hiddenScale BHist.Empty ∧ hsame hiddenChart BHist.Empty ∧
            ProjectiveVarVisibleCarrier chart homogeneous projective evaluation endpoint polyBundle
              tokenBundle pkg := by
  intro carrier hiddenCont hiddenEmpty
  have emptyCont : Cont hiddenScale hiddenChart BHist.Empty :=
    cont_result_hsame_transport hiddenCont hiddenEmpty
  have endpoints := cont_empty_result_inversion emptyCont
  exact And.intro endpoints.left (And.intro endpoints.right carrier)

end BEDC.Derived.ProjectiveVarUp
