import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.ProjectiveVarUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.ProjectiveVarUp
