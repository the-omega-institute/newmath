import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_ledger_exclusion [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger external :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      (hsame groupWord (BHist.e0 external) -> False) ∧
        (hsame groupWord (BHist.e1 external) -> False) ∧
          (hsame spinEndpoint (BHist.e0 external) -> False) := by
  intro carrier
  have sourceScope := SpinGroupRootCarrier_source_scope carrier
  have groupEmpty : hsame groupWord BHist.Empty :=
    sourceScope.right.left
  have spinUnary : UnaryHistory spinEndpoint :=
    sourceScope.right.right.left
  exact And.intro
    (by
      intro sameGroup
      exact not_hsame_e0_empty (hsame_trans (hsame_symm sameGroup) groupEmpty))
    (And.intro
      (by
        intro sameGroup
        exact not_hsame_e1_empty (hsame_trans (hsame_symm sameGroup) groupEmpty))
      (by
        intro sameSpin
        exact unary_no_zero_extension (unary_transport spinUnary sameSpin)))

end BEDC.Derived.SpinGroupUp
