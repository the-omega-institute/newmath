import BEDC.Derived.SpinGroupUp

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.CliffordUp
open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SpinGroupRootCarrier_transport_closure [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint cliffordEndpoint' groupWord groupWord'
      spinEndpoint spinEndpoint' ledger transportLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame cliffordEndpoint cliffordEndpoint' ->
        hsame groupWord groupWord' ->
          Cont product boundary cliffordEndpoint' ->
            Cont cliffordEndpoint' groupWord' spinEndpoint' ->
              Cont spinEndpoint' groupWord' transportLedger ->
                SpinGroupRootCarrier unit vector product boundary cliffordEndpoint' groupWord'
                    spinEndpoint' ledger bundle pkg ∧
                  hsame spinEndpoint spinEndpoint' ∧ UnaryHistory transportLedger ∧
                    hsame transportLedger (append spinEndpoint' groupWord') ∧
                      PkgSig bundle ledger pkg := by
  intro carrier sameClifford sameGroup productBoundary spinCont transportCont
  have transported :=
    SpinGroupRootCarrier_group_law_transport carrier sameClifford sameGroup productBoundary spinCont
  have transportedScope := SpinGroupRootCarrier_source_scope transported.left
  have groupUnary' : UnaryHistory groupWord' :=
    unary_transport unary_empty (hsame_symm transportedScope.right.left)
  have transportUnary : UnaryHistory transportLedger :=
    unary_cont_closed transportedScope.right.right.left groupUnary' transportCont
  exact And.intro transported.left
    (And.intro transported.right
      (And.intro transportUnary
        (And.intro transportCont transportedScope.right.right.right.right)))

theorem SpinGroupRootCarrier_double_cover_fiber_ledger [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger unit' vector'
      product' boundary' cliffordEndpoint' groupWord' spinEndpoint' ledger' fiberLedger
      actionLedger : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      SpinGroupRootCarrier unit' vector' product' boundary' cliffordEndpoint' groupWord'
          spinEndpoint' ledger' bundle pkg ->
        Cont spinEndpoint spinEndpoint' fiberLedger ->
          Cont fiberLedger boundary actionLedger ->
            UnaryHistory fiberLedger ∧ UnaryHistory actionLedger ∧
              hsame fiberLedger (append spinEndpoint spinEndpoint') ∧
                hsame actionLedger (append fiberLedger boundary) ∧ PkgSig bundle ledger pkg := by
  intro carrier carrier' fiberCont actionCont
  have sourceScope :=
    SpinGroupRootCarrier_source_scope carrier
  have sourceScope' :=
    SpinGroupRootCarrier_source_scope carrier'
  have fiberUnary : UnaryHistory fiberLedger :=
    unary_cont_closed sourceScope.right.right.left sourceScope'.right.right.left fiberCont
  have actionUnary : UnaryHistory actionLedger :=
    unary_cont_closed fiberUnary carrier.left.right.right.left actionCont
  exact And.intro fiberUnary
    (And.intro actionUnary
      (And.intro fiberCont
        (And.intro actionCont sourceScope.right.right.right.right)))

end BEDC.Derived.SpinGroupUp
