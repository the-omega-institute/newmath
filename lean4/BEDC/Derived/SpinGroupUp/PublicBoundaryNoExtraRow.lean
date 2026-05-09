import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_public_boundary_no_extra_row [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger row extra :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame row spinEndpoint ->
        hsame extra (BHist.e1 row) ->
          UnaryHistory spinEndpoint ∧ (hsame extra spinEndpoint -> False) := by
  intro carrier sameRowSpin sameExtraStep
  have scope := SpinGroupRootCarrier_source_scope carrier
  exact And.intro scope.right.right.left (by
    intro sameExtraSpin
    have sameStepSpin : hsame (BHist.e1 row) spinEndpoint :=
      hsame_trans (hsame_symm sameExtraStep) sameExtraSpin
    have sameStepRow : hsame (BHist.e1 row) row :=
      hsame_trans sameStepSpin (hsame_symm sameRowSpin)
    exact hsame_extension_self_absurd.right row sameStepRow)

end BEDC.Derived.SpinGroupUp
