import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_conjugation_action_readback [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger inverseLedger
      actionLedger : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger
        bundle pkg ->
      Cont spinEndpoint groupWord inverseLedger ->
        Cont inverseLedger spinEndpoint actionLedger ->
          UnaryHistory inverseLedger ∧ UnaryHistory actionLedger ∧
            hsame inverseLedger (append spinEndpoint groupWord) ∧
              hsame actionLedger (append inverseLedger spinEndpoint) ∧ PkgSig bundle ledger pkg := by
  intro carrier inverseCont actionCont
  have sourceScope :=
    SpinGroupRootCarrier_source_scope carrier
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm sourceScope.right.left)
  have inverseUnary : UnaryHistory inverseLedger :=
    unary_cont_closed sourceScope.right.right.left groupUnary inverseCont
  have actionUnary : UnaryHistory actionLedger :=
    unary_cont_closed inverseUnary sourceScope.right.right.left actionCont
  exact And.intro inverseUnary
    (And.intro actionUnary
      (And.intro inverseCont
        (And.intro actionCont sourceScope.right.right.right.right)))

end BEDC.Derived.SpinGroupUp
