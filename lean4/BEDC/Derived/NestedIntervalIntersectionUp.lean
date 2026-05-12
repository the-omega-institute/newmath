import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NestedIntervalIntersectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NestedIntervalIntersectionCarrier [AskSetup] [PackageSetup]
    (sourceChain width selector endpoints handoff sealRow transport route name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceChain ∧ UnaryHistory width ∧ UnaryHistory selector ∧
    UnaryHistory endpoints ∧ UnaryHistory handoff ∧ UnaryHistory sealRow ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory name ∧
        Cont sourceChain width selector ∧ Cont selector endpoints handoff ∧
          Cont handoff sealRow transport ∧ Cont transport route name ∧
            PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem NestedIntervalIntersectionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {sourceChain width selector endpoints handoff sealRow transport route name : BHist} :
    NestedIntervalIntersectionCarrier sourceChain width selector endpoints handoff sealRow
        transport route name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          NestedIntervalIntersectionCarrier sourceChain width selector endpoints handoff sealRow
            transport route name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          NestedIntervalIntersectionCarrier sourceChain width selector endpoints handoff sealRow
            transport route name bundle pkg ∧ hsame row sealRow)
        (fun row : BHist =>
          NestedIntervalIntersectionCarrier sourceChain width selector endpoints handoff sealRow
            transport route name bundle pkg ∧ hsame row sealRow)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro sealRow (And.intro carrier (hsame_refl sealRow))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem NestedIntervalIntersectionCarrier_finite_diagonal_handoff [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {sourceChain width selector endpoints handoff sealRow transport route name selectedRead : BHist} :
    NestedIntervalIntersectionCarrier sourceChain width selector endpoints handoff sealRow transport
        route name bundle pkg ->
      Cont selector endpoints selectedRead ->
        UnaryHistory selectedRead ∧ UnaryHistory handoff ∧ Cont selector endpoints selectedRead ∧
          Cont selector endpoints handoff ∧ PkgSig bundle route pkg := by
  intro carrier selectedReadRoute
  cases carrier with
  | intro sourceChainUnary carrier =>
      cases carrier with
      | intro widthUnary carrier =>
          cases carrier with
          | intro selectorUnary carrier =>
              cases carrier with
              | intro endpointsUnary carrier =>
                  cases carrier with
                  | intro handoffUnary carrier =>
                      cases carrier with
                      | intro sealRowUnary carrier =>
                          cases carrier with
                          | intro transportUnary carrier =>
                              cases carrier with
                              | intro routeUnary carrier =>
                                  cases carrier with
                                  | intro nameUnary carrier =>
                                      cases carrier with
                                      | intro sourceRoute carrier =>
                                          cases carrier with
                                          | intro handoffRoute carrier =>
                                              cases carrier with
                                              | intro transportRoute carrier =>
                                                  cases carrier with
                                                  | intro nameRoute carrier =>
                                                      cases carrier with
                                                      | intro routePkg namePkg =>
                                                          have selectedReadUnary :
                                                              UnaryHistory selectedRead :=
                                                            unary_cont_closed selectorUnary
                                                              endpointsUnary selectedReadRoute
                                                          exact
                                                            ⟨selectedReadUnary, handoffUnary,
                                                              selectedReadRoute, handoffRoute,
                                                              routePkg⟩

theorem NestedIntervalIntersectionCarrier_selector_transport_determinacy [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {sourceChain width selector endpoints handoff sealRow transport route name sourceChain' width'
      selector' endpoints' handoff' sealRow' transport' : BHist} :
    NestedIntervalIntersectionCarrier sourceChain width selector endpoints handoff sealRow
        transport route name bundle pkg ->
      hsame sourceChain sourceChain' ->
        hsame width width' ->
          hsame selector selector' ->
            hsame endpoints endpoints' ->
              hsame sealRow sealRow' ->
                hsame transport transport' ->
                  Cont sourceChain' width' selector' ->
                    Cont selector' endpoints' handoff' ->
                      Cont handoff' sealRow' transport' ->
                        hsame handoff handoff' ∧
                          NestedIntervalIntersectionCarrier sourceChain' width' selector'
                            endpoints' handoff' sealRow' transport' route name bundle pkg := by
  intro carrier sameSource sameWidth sameSelector sameEndpoints sameSeal sameTransport
  intro contSource contSelector contHandoff
  have sourceUnary : UnaryHistory sourceChain' :=
    unary_transport carrier.left sameSource
  have widthUnary : UnaryHistory width' :=
    unary_transport carrier.right.left sameWidth
  have selectorUnary : UnaryHistory selector' :=
    unary_transport carrier.right.right.left sameSelector
  have endpointsUnary : UnaryHistory endpoints' :=
    unary_transport carrier.right.right.right.left sameEndpoints
  have handoffSame : hsame handoff handoff' :=
    cont_respects_hsame sameSelector sameEndpoints carrier.right.right.right.right.right.right.right.right.right.right.left contSelector
  have handoffUnary : UnaryHistory handoff' :=
    unary_transport carrier.right.right.right.right.left handoffSame
  have sealUnary : UnaryHistory sealRow' :=
    unary_transport carrier.right.right.right.right.right.left sameSeal
  have transportUnary : UnaryHistory transport' :=
    unary_transport carrier.right.right.right.right.right.right.left sameTransport
  have transportedRoute : Cont transport' route name := by
    cases sameTransport
    exact carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  exact And.intro handoffSame
    (And.intro sourceUnary
      (And.intro widthUnary
        (And.intro selectorUnary
          (And.intro endpointsUnary
            (And.intro handoffUnary
              (And.intro sealUnary
                (And.intro transportUnary
                  (And.intro carrier.right.right.right.right.right.right.right.left
                    (And.intro carrier.right.right.right.right.right.right.right.right.left
                      (And.intro contSource
                        (And.intro contSelector
                          (And.intro contHandoff
                            (And.intro transportedRoute
                              (And.intro carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.left
                                carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right))))))))))))))

end BEDC.Derived.NestedIntervalIntersectionUp
