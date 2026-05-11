import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ControlControllabilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ControlControllabilityCarrier [AskSetup] [PackageSetup]
    (state input transition control horizon columns matrix contRows endpoint : BHist)
    (probe : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
    UnaryHistory control ∧ UnaryHistory horizon ∧ UnaryHistory columns ∧
      UnaryHistory matrix ∧ UnaryHistory contRows ∧ UnaryHistory endpoint ∧
        Cont transition control columns ∧ Cont columns matrix endpoint ∧
          Cont contRows horizon endpoint ∧ PkgSig probe endpoint pkg

theorem ControlControllabilityCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {state input transition control horizon columns matrix contRows endpoint : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlControllabilityCarrier state input transition control horizon columns matrix contRows
        endpoint probe pkg ->
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) (fun h : BHist => hsame h endpoint)
          hsame ∧
        Cont transition control columns ∧ Cont columns matrix endpoint ∧
          Cont contRows horizon endpoint ∧ PkgSig probe endpoint pkg := by
  intro carrier
  have cert :
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) (fun h : BHist => hsame h endpoint)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact hsame_trans (hsame_symm sameRows) sourceRow
    }
    pattern_sound := by
      intro _row sourceRow
      exact sourceRow
    ledger_sound := by
      intro _row sourceRow
      exact sourceRow
  }
  exact And.intro cert
    (And.intro carrier.right.right.right.right.right.right.right.right.right.left
      (And.intro carrier.right.right.right.right.right.right.right.right.right.right.left
        (And.intro carrier.right.right.right.right.right.right.right.right.right.right.right.left
          carrier.right.right.right.right.right.right.right.right.right.right.right.right)))

theorem ControlControllabilityCarrier_classifier_stability_obligation [AskSetup] [PackageSetup]
    {state input transition control horizon columns matrix contRows endpoint state' input'
      transition' control' horizon' columns' matrix' contRows' endpoint' : BHist}
    {probe : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlControllabilityCarrier state input transition control horizon columns matrix contRows
        endpoint probe pkg ->
      hsame state state' ->
        hsame input input' ->
          hsame transition transition' ->
            hsame control control' ->
              hsame horizon horizon' ->
                hsame matrix matrix' ->
                  hsame contRows contRows' ->
                    Cont transition' control' columns' ->
                      Cont columns' matrix' endpoint' ->
                        Cont contRows' horizon' endpoint' ->
                          PkgSig probe endpoint' pkg ->
                            ControlControllabilityCarrier state' input' transition' control'
                                horizon' columns' matrix' contRows' endpoint' probe pkg ∧
                              hsame columns columns' ∧ hsame endpoint endpoint' := by
  intro carrier sameState sameInput sameTransition sameControl sameHorizon sameMatrix
    sameContRows transitionControlColumns columnsMatrixEndpoint contRowsHorizonEndpoint pkgSig
  rcases carrier with
    ⟨stateUnary, inputUnary, transitionUnary, controlUnary, horizonUnary, _columnsUnary,
      matrixUnary, contRowsUnary, _endpointUnary, transitionControlColumnsOld,
      columnsMatrixEndpointOld, _contRowsHorizonEndpointOld, _pkgSigOld⟩
  have stateUnary' : UnaryHistory state' :=
    unary_transport stateUnary sameState
  have inputUnary' : UnaryHistory input' :=
    unary_transport inputUnary sameInput
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport transitionUnary sameTransition
  have controlUnary' : UnaryHistory control' :=
    unary_transport controlUnary sameControl
  have horizonUnary' : UnaryHistory horizon' :=
    unary_transport horizonUnary sameHorizon
  have matrixUnary' : UnaryHistory matrix' :=
    unary_transport matrixUnary sameMatrix
  have contRowsUnary' : UnaryHistory contRows' :=
    unary_transport contRowsUnary sameContRows
  have sameColumns : hsame columns columns' :=
    cont_respects_hsame sameTransition sameControl transitionControlColumnsOld
      transitionControlColumns
  have columnsUnary' : UnaryHistory columns' :=
    unary_cont_closed transitionUnary' controlUnary' transitionControlColumns
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameColumns sameMatrix columnsMatrixEndpointOld columnsMatrixEndpoint
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_cont_closed columnsUnary' matrixUnary' columnsMatrixEndpoint
  exact
    ⟨⟨stateUnary', inputUnary', transitionUnary', controlUnary', horizonUnary', columnsUnary',
        matrixUnary', contRowsUnary', endpointUnary', transitionControlColumns,
        columnsMatrixEndpoint, contRowsHorizonEndpoint, pkgSig⟩,
      sameColumns, sameEndpoint⟩

def ControlControllabilityReachabilityPacket [AskSetup] [PackageSetup]
    (state input transition control horizon firstColumn reachability provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
    UnaryHistory control ∧ UnaryHistory horizon ∧ UnaryHistory provenance ∧
      Cont control horizon firstColumn ∧ Cont firstColumn transition reachability ∧
        Cont reachability provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ControlControllabilityReachabilityPacket_reachability_ledger [AskSetup]
    [PackageSetup] {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {state input transition control horizon firstColumn reachability provenance endpoint : BHist} :
    ControlControllabilityReachabilityPacket state input transition control horizon firstColumn
        reachability provenance endpoint bundle pkg ->
      UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
        UnaryHistory control ∧ UnaryHistory horizon ∧ UnaryHistory firstColumn ∧
          UnaryHistory reachability ∧ hsame firstColumn (append control horizon) ∧
            hsame reachability (append firstColumn transition) ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have stateUnary : UnaryHistory state :=
    packet.left
  have inputUnary : UnaryHistory input :=
    packet.right.left
  have transitionUnary : UnaryHistory transition :=
    packet.right.right.left
  have controlUnary : UnaryHistory control :=
    packet.right.right.right.left
  have horizonUnary : UnaryHistory horizon :=
    packet.right.right.right.right.left
  have firstColumnRow : Cont control horizon firstColumn :=
    packet.right.right.right.right.right.right.left
  have reachabilityRow : Cont firstColumn transition reachability :=
    packet.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right
  have firstColumnUnary : UnaryHistory firstColumn :=
    unary_cont_closed controlUnary horizonUnary firstColumnRow
  have reachabilityUnary : UnaryHistory reachability :=
    unary_cont_closed firstColumnUnary transitionUnary reachabilityRow
  exact And.intro stateUnary
    (And.intro inputUnary
      (And.intro transitionUnary
        (And.intro controlUnary
          (And.intro horizonUnary
            (And.intro firstColumnUnary
              (And.intro reachabilityUnary
                (And.intro firstColumnRow (And.intro reachabilityRow pkgSig))))))))

theorem ControlControllabilityReachabilityPacket_dependency_scope [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {state input transition control horizon firstColumn reachability provenance endpoint : BHist} :
    ControlControllabilityReachabilityPacket state input transition control horizon firstColumn
        reachability provenance endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ControlControllabilityReachabilityPacket state input transition control horizon
                firstColumn reachability provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ControlControllabilityReachabilityPacket state input transition control horizon
                firstColumn reachability provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ControlControllabilityReachabilityPacket state input transition control horizon
                firstColumn reachability provenance e bundle pkg ∧ hsame row e)
          hsame ∧
        Cont control horizon firstColumn ∧ Cont firstColumn transition reachability ∧
          Cont reachability provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have endpointSource :
      (fun row : BHist =>
        exists e : BHist,
          ControlControllabilityReachabilityPacket state input transition control horizon firstColumn
            reachability provenance e bundle pkg ∧ hsame row e) endpoint :=
    Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            exists e : BHist,
              ControlControllabilityReachabilityPacket state input transition control horizon
                firstColumn reachability provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ControlControllabilityReachabilityPacket state input transition control horizon
                firstColumn reachability provenance e bundle pkg ∧ hsame row e)
          (fun row : BHist =>
            exists e : BHist,
              ControlControllabilityReachabilityPacket state input transition control horizon
                firstColumn reachability provenance e bundle pkg ∧ hsame row e)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSource
      equiv_refl := by
        intro row _carrier
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' sameRows carrierRow
        cases carrierRow with
        | intro e endpointWitness =>
            exact Exists.intro e
              (And.intro endpointWitness.left
                (hsame_trans (hsame_symm sameRows) endpointWitness.right))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  exact And.intro cert
    (And.intro packet.right.right.right.right.right.right.left
      (And.intro packet.right.right.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right.right.right.left
          packet.right.right.right.right.right.right.right.right.right)))

theorem ControlControllabilityReachabilityPacket_consumer_boundary [AskSetup]
    [PackageSetup] {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {state input transition control horizon firstColumn reachability provenance endpoint : BHist} :
    ControlControllabilityReachabilityPacket state input transition control horizon firstColumn
        reachability provenance endpoint bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          hsame ∧
        UnaryHistory state ∧ UnaryHistory input ∧ UnaryHistory transition ∧
          UnaryHistory control ∧ UnaryHistory horizon ∧ UnaryHistory firstColumn ∧
            UnaryHistory reachability ∧ Cont control horizon firstColumn ∧
              Cont firstColumn transition reachability ∧
                Cont reachability provenance endpoint ∧ PkgSig bundle endpoint pkg := by
  intro packet
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          (fun row : BHist =>
            ControlControllabilityReachabilityPacket state input transition control horizon
              firstColumn reachability provenance endpoint bundle pkg ∧ hsame row endpoint)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro packet (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }
  have firstColumnUnary : UnaryHistory firstColumn :=
    unary_cont_closed packet.right.right.right.left packet.right.right.right.right.left
      packet.right.right.right.right.right.right.left
  have reachabilityUnary : UnaryHistory reachability :=
    unary_cont_closed firstColumnUnary packet.right.right.left
      packet.right.right.right.right.right.right.right.left
  exact And.intro cert
    (And.intro packet.left
      (And.intro packet.right.left
        (And.intro packet.right.right.left
          (And.intro packet.right.right.right.left
            (And.intro packet.right.right.right.right.left
              (And.intro firstColumnUnary
                (And.intro reachabilityUnary
                  (And.intro packet.right.right.right.right.right.right.left
                    (And.intro packet.right.right.right.right.right.right.right.left
                      (And.intro packet.right.right.right.right.right.right.right.right.left
                        packet.right.right.right.right.right.right.right.right.right))))))))))

theorem ControlControllabilityReachabilityPacket_column_transport_obligation [AskSetup]
    [PackageSetup] {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {state input transition control horizon firstColumn reachability provenance endpoint state' input'
      transition' control' horizon' firstColumn' reachability' provenance' endpoint' : BHist} :
    ControlControllabilityReachabilityPacket state input transition control horizon firstColumn
        reachability provenance endpoint bundle pkg ->
      hsame state state' ->
        hsame input input' ->
          hsame transition transition' ->
            hsame control control' ->
              hsame horizon horizon' ->
                hsame provenance provenance' ->
                  Cont control' horizon' firstColumn' ->
                    Cont firstColumn' transition' reachability' ->
                      Cont reachability' provenance' endpoint' ->
                        PkgSig bundle endpoint' pkg ->
                          ControlControllabilityReachabilityPacket state' input' transition'
                              control' horizon' firstColumn' reachability' provenance' endpoint'
                              bundle pkg ∧
                            hsame firstColumn firstColumn' ∧ hsame reachability reachability' ∧
                              hsame endpoint endpoint' := by
  intro packet sameState sameInput sameTransition sameControl sameHorizon sameProvenance
    firstColumnRow' reachabilityRow' endpointRow' pkgSig'
  have stateUnary' : UnaryHistory state' :=
    unary_transport packet.left sameState
  have inputUnary' : UnaryHistory input' :=
    unary_transport packet.right.left sameInput
  have transitionUnary' : UnaryHistory transition' :=
    unary_transport packet.right.right.left sameTransition
  have controlUnary' : UnaryHistory control' :=
    unary_transport packet.right.right.right.left sameControl
  have horizonUnary' : UnaryHistory horizon' :=
    unary_transport packet.right.right.right.right.left sameHorizon
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport packet.right.right.right.right.right.left sameProvenance
  have firstColumnRow : Cont control horizon firstColumn :=
    packet.right.right.right.right.right.right.left
  have reachabilityRow : Cont firstColumn transition reachability :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont reachability provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have sameFirstColumn : hsame firstColumn firstColumn' :=
    cont_respects_hsame sameControl sameHorizon firstColumnRow firstColumnRow'
  have sameReachability : hsame reachability reachability' :=
    cont_respects_hsame sameFirstColumn sameTransition reachabilityRow reachabilityRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameReachability sameProvenance endpointRow endpointRow'
  have transportedPacket :
      ControlControllabilityReachabilityPacket state' input' transition' control' horizon'
        firstColumn' reachability' provenance' endpoint' bundle pkg :=
    And.intro stateUnary'
      (And.intro inputUnary'
        (And.intro transitionUnary'
          (And.intro controlUnary'
            (And.intro horizonUnary'
              (And.intro provenanceUnary'
                (And.intro firstColumnRow'
                  (And.intro reachabilityRow' (And.intro endpointRow' pkgSig'))))))))
  exact And.intro transportedPacket
    (And.intro sameFirstColumn (And.intro sameReachability sameEndpoint))

theorem ControlControllabilityReachabilityPacket_continuation_closure [AskSetup]
    [PackageSetup]
    {state input transition control horizon firstColumn reachability provenance endpoint
      endpointNext joinedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ControlControllabilityReachabilityPacket state input transition control horizon firstColumn
        reachability provenance endpoint bundle pkg ->
      UnaryHistory endpointNext ->
        Cont endpoint endpointNext joinedEndpoint ->
          PkgSig bundle joinedEndpoint pkg ->
            ∃ joinedProvenance : BHist,
              ControlControllabilityReachabilityPacket state input transition control horizon
                  firstColumn reachability joinedProvenance joinedEndpoint bundle pkg ∧
                hsame joinedProvenance (append provenance endpointNext) := by
  intro packet endpointNextUnary endpointJoin pkgSig
  have stateUnary : UnaryHistory state := packet.left
  have inputUnary : UnaryHistory input := packet.right.left
  have transitionUnary : UnaryHistory transition := packet.right.right.left
  have controlUnary : UnaryHistory control := packet.right.right.right.left
  have horizonUnary : UnaryHistory horizon := packet.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance := packet.right.right.right.right.right.left
  have firstColumnRow : Cont control horizon firstColumn :=
    packet.right.right.right.right.right.right.left
  have reachabilityRow : Cont firstColumn transition reachability :=
    packet.right.right.right.right.right.right.right.left
  have endpointRow : Cont reachability provenance endpoint :=
    packet.right.right.right.right.right.right.right.right.left
  have joinedRows := cont_assoc_middle_exists endpointRow endpointJoin
  cases joinedRows with
  | intro joinedProvenance joinedData =>
      have joinedProvenanceUnary : UnaryHistory joinedProvenance :=
        unary_cont_closed provenanceUnary endpointNextUnary joinedData.left
      exact Exists.intro joinedProvenance
        (And.intro
          (And.intro stateUnary
            (And.intro inputUnary
              (And.intro transitionUnary
                (And.intro controlUnary
                  (And.intro horizonUnary
                    (And.intro joinedProvenanceUnary
                      (And.intro firstColumnRow
                        (And.intro reachabilityRow
                          (And.intro joinedData.right pkgSig)))))))))
          joinedData.left)

end BEDC.Derived.ControlControllabilityUp
