import BEDC.Derived.CliffordUp
import BEDC.Derived.GroupUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.SpinGroupUp

open BEDC.Derived.CliffordUp
open BEDC.Derived.GroupUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SpinGroupRootCarrier [AskSetup] [PackageSetup]
    (unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
    GroupSingletonCarrier groupWord ∧ Cont cliffordEndpoint groupWord spinEndpoint ∧
      PkgSig bundle ledger pkg

theorem SpinGroupRootCarrier_source_scope [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
        GroupSingletonCarrier groupWord ∧ UnaryHistory spinEndpoint ∧
          Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have clifford : CliffordCarrierPackage unit vector product boundary cliffordEndpoint :=
    carrier.left
  have productUnary : UnaryHistory product :=
    unary_cont_closed clifford.right.left clifford.right.left clifford.right.right.right.left
  have endpointUnary : UnaryHistory cliffordEndpoint :=
    unary_cont_closed productUnary clifford.right.right.left clifford.right.right.right.right
  have groupUnary : UnaryHistory groupWord :=
    unary_transport unary_empty (hsame_symm carrier.right.left)
  have spinUnary : UnaryHistory spinEndpoint :=
    unary_cont_closed endpointUnary groupUnary carrier.right.right.left
  exact
    And.intro clifford
      (And.intro carrier.right.left
        (And.intro spinUnary
          (And.intro carrier.right.right.left carrier.right.right.right)))

theorem SpinGroupRootCarrier_group_law_transport [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint cliffordEndpoint' groupWord groupWord'
      spinEndpoint spinEndpoint' ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      hsame cliffordEndpoint cliffordEndpoint' ->
        hsame groupWord groupWord' ->
          Cont product boundary cliffordEndpoint' ->
            Cont cliffordEndpoint' groupWord' spinEndpoint' ->
              SpinGroupRootCarrier unit vector product boundary cliffordEndpoint' groupWord'
                  spinEndpoint' ledger bundle pkg ∧ hsame spinEndpoint spinEndpoint' := by
  intro carrier sameClifford sameGroup productBoundary spinCont
  have clifford' :
      CliffordCarrierPackage unit vector product boundary cliffordEndpoint' :=
    And.intro carrier.left.left
      (And.intro carrier.left.right.left
        (And.intro carrier.left.right.right.left
          (And.intro carrier.left.right.right.right.left productBoundary)))
  have group' : GroupSingletonCarrier groupWord' :=
    hsame_trans (hsame_symm sameGroup) carrier.right.left
  have sameSpin : hsame spinEndpoint spinEndpoint' :=
    cont_respects_hsame sameClifford sameGroup carrier.right.right.left spinCont
  exact
    And.intro
      (And.intro clifford'
        (And.intro group'
          (And.intro spinCont carrier.right.right.right)))
      sameSpin

theorem SpinGroupRootCarrier_public_consumer_boundary_coverage [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint groupWord spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SpinGroupRootCarrier unit vector product boundary cliffordEndpoint groupWord spinEndpoint
        ledger bundle pkg ->
      UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory product ∧ UnaryHistory boundary ∧
        UnaryHistory cliffordEndpoint ∧ GroupSingletonCarrier groupWord ∧
          UnaryHistory spinEndpoint ∧ Cont vector vector product ∧
            Cont product boundary cliffordEndpoint ∧
              Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have cliffordExact :
      UnaryHistory unit ∧ UnaryHistory vector ∧ UnaryHistory product ∧ UnaryHistory boundary ∧
        UnaryHistory cliffordEndpoint ∧ Cont vector vector product ∧
          Cont product boundary cliffordEndpoint ∧
            hsame product (append vector vector) ∧
              hsame cliffordEndpoint (append (append vector vector) boundary) :=
    CliffordCarrierPackage_universal_ledger_exactness carrier.left
  have sourceScope :
      CliffordCarrierPackage unit vector product boundary cliffordEndpoint ∧
        GroupSingletonCarrier groupWord ∧ UnaryHistory spinEndpoint ∧
          Cont cliffordEndpoint groupWord spinEndpoint ∧ PkgSig bundle ledger pkg :=
    SpinGroupRootCarrier_source_scope carrier
  exact
    And.intro cliffordExact.left
      (And.intro cliffordExact.right.left
        (And.intro cliffordExact.right.right.left
          (And.intro cliffordExact.right.right.right.left
            (And.intro cliffordExact.right.right.right.right.left
              (And.intro sourceScope.right.left
                (And.intro sourceScope.right.right.left
                  (And.intro cliffordExact.right.right.right.right.right.left
                    (And.intro cliffordExact.right.right.right.right.right.right.left
                      (And.intro sourceScope.right.right.right.left
                        sourceScope.right.right.right.right)))))))))

theorem SpinGroupRootCarrier_clifford_unit_lift [AskSetup] [PackageSetup]
    {unit vector product boundary cliffordEndpoint spinEndpoint ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CliffordCarrierPackage unit vector product boundary cliffordEndpoint ->
      Cont cliffordEndpoint BHist.Empty spinEndpoint ->
        PkgSig bundle ledger pkg ->
          SpinGroupRootCarrier unit vector product boundary cliffordEndpoint BHist.Empty
            spinEndpoint ledger bundle pkg ∧ hsame spinEndpoint cliffordEndpoint := by
  intro clifford endpointUnit packageSig
  exact And.intro
    (And.intro clifford
      (And.intro (hsame_refl BHist.Empty)
        (And.intro endpointUnit packageSig)))
    (cont_right_unit_result endpointUnit)

end BEDC.Derived.SpinGroupUp
