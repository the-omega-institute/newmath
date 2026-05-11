import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.NestedIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NestedIntervalFinitePacket [AskSetup] [PackageSetup]
    (interval endpoint width schedule regular sealRow transportRow provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory interval ∧ UnaryHistory endpoint ∧ UnaryHistory width ∧
    UnaryHistory schedule ∧ UnaryHistory regular ∧ UnaryHistory sealRow ∧
      UnaryHistory transportRow ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont interval endpoint width ∧ Cont width schedule regular ∧
          Cont regular sealRow transportRow ∧ Cont transportRow provenance cert ∧
            PkgSig bundle cert pkg

theorem NestedIntervalFinitePacket_endpoint_transport [AskSetup] [PackageSetup]
    {interval endpoint width schedule regular sealRow transportRow provenance cert interval'
      endpoint' width' schedule' regular' sealRow' transportRow' provenance' cert' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFinitePacket interval endpoint width schedule regular sealRow transportRow
        provenance cert bundle pkg ->
      hsame interval interval' ->
        hsame endpoint endpoint' ->
          hsame schedule schedule' ->
            hsame sealRow sealRow' ->
              hsame provenance provenance' ->
                Cont interval' endpoint' width' ->
                  Cont width' schedule' regular' ->
                    Cont regular' sealRow' transportRow' ->
                      Cont transportRow' provenance' cert' ->
                        PkgSig bundle cert' pkg ->
                          NestedIntervalFinitePacket interval' endpoint' width' schedule' regular'
                              sealRow' transportRow' provenance' cert' bundle pkg ∧
                            hsame width width' ∧ hsame regular regular' ∧ hsame cert cert' := by
  intro packet sameInterval sameEndpoint sameSchedule sameSealRow sameProvenance
  intro widthRow' regularRow' transportRowRow' certRow' pkgRow'
  obtain ⟨intervalUnary, endpointUnary, _widthUnary, scheduleUnary, _regularUnary,
    sealRowUnary, _transportRowUnary, provenanceUnary, _certUnary, widthRow, regularRow,
    transportRowRow, certRow, _pkgRow⟩ := packet
  have intervalUnary' : UnaryHistory interval' :=
    unary_transport intervalUnary sameInterval
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have scheduleUnary' : UnaryHistory schedule' :=
    unary_transport scheduleUnary sameSchedule
  have sealRowUnary' : UnaryHistory sealRow' :=
    unary_transport sealRowUnary sameSealRow
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have widthUnary' : UnaryHistory width' :=
    unary_cont_closed intervalUnary' endpointUnary' widthRow'
  have regularUnary' : UnaryHistory regular' :=
    unary_cont_closed widthUnary' scheduleUnary' regularRow'
  have transportRowUnary' : UnaryHistory transportRow' :=
    unary_cont_closed regularUnary' sealRowUnary' transportRowRow'
  have certUnary' : UnaryHistory cert' :=
    unary_cont_closed transportRowUnary' provenanceUnary' certRow'
  have sameWidth : hsame width width' :=
    cont_respects_hsame sameInterval sameEndpoint widthRow widthRow'
  have sameRegular : hsame regular regular' :=
    cont_respects_hsame sameWidth sameSchedule regularRow regularRow'
  have sameTransportRow : hsame transportRow transportRow' :=
    cont_respects_hsame sameRegular sameSealRow transportRowRow transportRowRow'
  have sameCert : hsame cert cert' :=
    cont_respects_hsame sameTransportRow sameProvenance certRow certRow'
  constructor
  · exact ⟨intervalUnary', endpointUnary', widthUnary', scheduleUnary', regularUnary',
      sealRowUnary', transportRowUnary', provenanceUnary', certUnary', widthRow', regularRow',
      transportRowRow', certRow', pkgRow'⟩
  · exact ⟨sameWidth, sameRegular, sameCert⟩

def NestedIntervalFiniteCarrier [AskSetup] [PackageSetup]
    (lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory order ∧ UnaryHistory width ∧
    UnaryHistory inclusion ∧ UnaryHistory schedule ∧ UnaryHistory regRead ∧
      UnaryHistory sealFace ∧ UnaryHistory endpoint ∧ UnaryHistory pkgLedger ∧
        Cont lower upper endpoint ∧ Cont endpoint order pkgLedger ∧ PkgSig bundle pkgLedger pkg

theorem NestedIntervalFiniteCarrier_endpoint_transport [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger lower' upper'
      order' width' inclusion' schedule' regRead' sealFace' endpoint' pkgLedger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace endpoint
        pkgLedger bundle pkg ->
      hsame lower lower' ->
        hsame upper upper' ->
          hsame order order' ->
            hsame width width' ->
              hsame inclusion inclusion' ->
                hsame schedule schedule' ->
                  hsame regRead regRead' ->
                    hsame sealFace sealFace' ->
                      Cont lower' upper' endpoint' ->
                        Cont endpoint' order' pkgLedger' ->
                          PkgSig bundle pkgLedger' pkg ->
                            NestedIntervalFiniteCarrier lower' upper' order' width' inclusion'
                                schedule' regRead' sealFace' endpoint' pkgLedger' bundle pkg ∧
                              hsame endpoint endpoint' ∧ hsame pkgLedger pkgLedger' := by
  intro carrier sameLower sameUpper sameOrder sameWidth sameInclusion sameSchedule sameRegRead
    sameSealFace endpointRow' ledgerRow' pkgRow'
  cases carrier with
  | intro lowerUnary rest =>
      cases rest with
      | intro upperUnary rest =>
          cases rest with
          | intro orderUnary rest =>
              cases rest with
              | intro widthUnary rest =>
                  cases rest with
                  | intro inclusionUnary rest =>
                      cases rest with
                      | intro scheduleUnary rest =>
                          cases rest with
                          | intro regReadUnary rest =>
                              cases rest with
                              | intro sealFaceUnary rest =>
                                  cases rest with
                                  | intro _endpointUnary rest =>
                                      cases rest with
                                      | intro _pkgLedgerUnary rest =>
                                          cases rest with
                                          | intro endpointRow rest =>
                                              cases rest with
                                              | intro ledgerRow _pkgRow =>
                                                  have lowerUnary' : UnaryHistory lower' :=
                                                    unary_transport lowerUnary sameLower
                                                  have upperUnary' : UnaryHistory upper' :=
                                                    unary_transport upperUnary sameUpper
                                                  have orderUnary' : UnaryHistory order' :=
                                                    unary_transport orderUnary sameOrder
                                                  have widthUnary' : UnaryHistory width' :=
                                                    unary_transport widthUnary sameWidth
                                                  have inclusionUnary' : UnaryHistory inclusion' :=
                                                    unary_transport inclusionUnary sameInclusion
                                                  have scheduleUnary' : UnaryHistory schedule' :=
                                                    unary_transport scheduleUnary sameSchedule
                                                  have regReadUnary' : UnaryHistory regRead' :=
                                                    unary_transport regReadUnary sameRegRead
                                                  have sealFaceUnary' : UnaryHistory sealFace' :=
                                                    unary_transport sealFaceUnary sameSealFace
                                                  have endpointUnary' : UnaryHistory endpoint' :=
                                                    unary_cont_closed lowerUnary' upperUnary'
                                                      endpointRow'
                                                  have pkgLedgerUnary' : UnaryHistory pkgLedger' :=
                                                    unary_cont_closed endpointUnary' orderUnary'
                                                      ledgerRow'
                                                  have sameEndpoint : hsame endpoint endpoint' :=
                                                    cont_respects_hsame sameLower sameUpper
                                                      endpointRow endpointRow'
                                                  have sameLedger : hsame pkgLedger pkgLedger' :=
                                                    cont_respects_hsame sameEndpoint sameOrder
                                                      ledgerRow ledgerRow'
                                                  exact
                                                    ⟨⟨lowerUnary', upperUnary', orderUnary',
                                                      widthUnary', inclusionUnary',
                                                      scheduleUnary', regReadUnary',
                                                      sealFaceUnary', endpointUnary',
                                                      pkgLedgerUnary', endpointRow', ledgerRow',
                                                      pkgRow'⟩, sameEndpoint, sameLedger⟩

theorem NestedIntervalFiniteCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
        endpoint pkgLedger bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
              endpoint pkgLedger bundle pkg ∧
            (hsame row endpoint ∨ hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
              endpoint pkgLedger bundle pkg ∧
            (hsame row endpoint ∨ hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
              endpoint pkgLedger bundle pkg ∧
            (hsame row endpoint ∨ hsame row pkgLedger))
        hsame := by
  intro carrier
  have sourceAtEndpoint :
      NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
          endpoint pkgLedger bundle pkg ∧
        (hsame endpoint endpoint ∨ hsame endpoint pkgLedger) :=
    ⟨carrier, Or.inl (hsame_refl endpoint)⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        refine ⟨source.left, ?_⟩
        cases source.right with
        | inl sameEndpoint =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameEndpoint)
        | inr sameLedger =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameLedger)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem NestedIntervalPacket_window_refinement [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger extra lower'
      upper' order' width' inclusion' schedule' regRead' sealFace' endpoint' pkgLedger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace endpoint
        pkgLedger bundle pkg ->
      UnaryHistory extra ->
        Cont lower extra lower' ->
          Cont upper extra upper' ->
            Cont order extra order' ->
              Cont width extra width' ->
                Cont inclusion extra inclusion' ->
                  Cont schedule extra schedule' ->
                    Cont regRead extra regRead' ->
                      Cont sealFace extra sealFace' ->
                        Cont lower' upper' endpoint' ->
                          Cont endpoint' order' pkgLedger' ->
                            PkgSig bundle pkgLedger' pkg ->
                              NestedIntervalFiniteCarrier lower' upper' order' width' inclusion'
                                schedule' regRead' sealFace' endpoint' pkgLedger' bundle pkg := by
  intro carrier extraUnary lowerRow upperRow orderRow widthRow inclusionRow scheduleRow regReadRow
    sealFaceRow endpointRow ledgerRow pkgRow
  cases carrier with
  | intro lowerUnary rest =>
      cases rest with
      | intro upperUnary rest =>
          cases rest with
          | intro orderUnary rest =>
              cases rest with
              | intro widthUnary rest =>
                  cases rest with
                  | intro inclusionUnary rest =>
                      cases rest with
                      | intro scheduleUnary rest =>
                          cases rest with
                          | intro regReadUnary rest =>
                              cases rest with
                              | intro sealFaceUnary rest =>
                                  have lowerUnary' : UnaryHistory lower' :=
                                    unary_cont_closed lowerUnary extraUnary lowerRow
                                  have upperUnary' : UnaryHistory upper' :=
                                    unary_cont_closed upperUnary extraUnary upperRow
                                  have orderUnary' : UnaryHistory order' :=
                                    unary_cont_closed orderUnary extraUnary orderRow
                                  have widthUnary' : UnaryHistory width' :=
                                    unary_cont_closed widthUnary extraUnary widthRow
                                  have inclusionUnary' : UnaryHistory inclusion' :=
                                    unary_cont_closed inclusionUnary extraUnary inclusionRow
                                  have scheduleUnary' : UnaryHistory schedule' :=
                                    unary_cont_closed scheduleUnary extraUnary scheduleRow
                                  have regReadUnary' : UnaryHistory regRead' :=
                                    unary_cont_closed regReadUnary extraUnary regReadRow
                                  have sealFaceUnary' : UnaryHistory sealFace' :=
                                    unary_cont_closed sealFaceUnary extraUnary sealFaceRow
                                  have endpointUnary' : UnaryHistory endpoint' :=
                                    unary_cont_closed lowerUnary' upperUnary' endpointRow
                                  have pkgLedgerUnary' : UnaryHistory pkgLedger' :=
                                    unary_cont_closed endpointUnary' orderUnary' ledgerRow
                                  exact
                                    ⟨lowerUnary', upperUnary', orderUnary', widthUnary',
                                      inclusionUnary', scheduleUnary', regReadUnary',
                                      sealFaceUnary', endpointUnary', pkgLedgerUnary',
                                      endpointRow, ledgerRow, pkgRow⟩

def NestedIntervalRegSeqRatWindow [AskSetup] [PackageSetup]
    (unaryPrefix lower upper width inclusion schedule regRead provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory unaryPrefix ∧ UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory width ∧
    UnaryHistory inclusion ∧ UnaryHistory schedule ∧ UnaryHistory regRead ∧
      UnaryHistory provenance ∧ UnaryHistory cert ∧ Cont lower upper width ∧
        Cont width inclusion regRead ∧ PkgSig bundle regRead pkg

theorem NestedIntervalRegSeqRatWindow_handoff [AskSetup] [PackageSetup]
    {unaryPrefix lower upper width inclusion schedule regRead provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalRegSeqRatWindow unaryPrefix lower upper width inclusion schedule regRead
        provenance cert bundle pkg ->
      UnaryHistory unaryPrefix ∧ UnaryHistory lower ∧ UnaryHistory upper ∧
        UnaryHistory width ∧ UnaryHistory inclusion ∧ UnaryHistory schedule ∧
          UnaryHistory regRead ∧ Cont lower upper width ∧ Cont width inclusion regRead ∧
            PkgSig bundle regRead pkg := by
  intro window
  obtain ⟨prefixUnary, lowerUnary, upperUnary, widthUnary, inclusionUnary, scheduleUnary,
    regReadUnary, _provenanceUnary, _certUnary, lowerUpperRow, widthInclusionRow,
    pkgRow⟩ := window
  have prefixHistory : UnaryHistory unaryPrefix := prefixUnary
  have lowerHistory : UnaryHistory lower := lowerUnary
  have upperHistory : UnaryHistory upper := upperUnary
  have widthHistory : UnaryHistory width := widthUnary
  have inclusionHistory : UnaryHistory inclusion := inclusionUnary
  have scheduleHistory : UnaryHistory schedule := scheduleUnary
  have regReadHistory : UnaryHistory regRead := regReadUnary
  have lowerUpper : Cont lower upper width := lowerUpperRow
  have widthInclusion : Cont width inclusion regRead := widthInclusionRow
  have regReadPkg : PkgSig bundle regRead pkg := pkgRow
  exact
    ⟨prefixHistory, lowerHistory, upperHistory, widthHistory, inclusionHistory, scheduleHistory,
      regReadHistory, lowerUpper, widthInclusion, regReadPkg⟩

theorem NestedIntervalFiniteCarrier_consumer_bridge_boundary [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger provenance
      cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace endpoint
        pkgLedger bundle pkg ->
      NestedIntervalRegSeqRatWindow schedule lower upper width inclusion schedule regRead provenance
        cert bundle pkg ->
        hsame order inclusion ->
          hsame endpoint width ∧ hsame pkgLedger regRead ∧ PkgSig bundle regRead pkg := by
  intro carrier window sameOrderInclusion
  obtain ⟨_lowerUnary, _upperUnary, _orderUnary, _widthUnary, _inclusionUnary, _scheduleUnary,
    _regReadUnary, _sealFaceUnary, _endpointUnary, _pkgLedgerUnary, endpointRow, ledgerRow,
    _carrierPkg⟩ := carrier
  obtain ⟨_scheduleUnaryWindow, _lowerUnaryWindow, _upperUnaryWindow, _widthUnaryWindow,
    _inclusionUnaryWindow, _scheduleUnaryWindow', _regReadUnaryWindow, _provenanceUnary,
    _certUnary, lowerUpperWidthRow, widthInclusionRow, regReadPkg⟩ := window
  have sameEndpointWidth : hsame endpoint width :=
    cont_respects_hsame (hsame_refl lower) (hsame_refl upper) endpointRow lowerUpperWidthRow
  have sameLedgerRegRead : hsame pkgLedger regRead :=
    cont_respects_hsame sameEndpointWidth sameOrderInclusion ledgerRow widthInclusionRow
  exact ⟨sameEndpointWidth, sameLedgerRegRead, regReadPkg⟩

theorem NestedIntervalPacket_consumer_bridge_finite_route_exactness [AskSetup] [PackageSetup]
    {unaryPrefix lower upper width inclusion schedule regRead provenance cert bridgeRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalRegSeqRatWindow unaryPrefix lower upper width inclusion schedule regRead
        provenance cert bundle pkg ->
      Cont regRead cert bridgeRoute ->
        PkgSig bundle bridgeRoute pkg ->
          UnaryHistory bridgeRoute ∧ hsame width (append lower upper) ∧
            hsame regRead (append width inclusion) ∧ Cont regRead cert bridgeRoute ∧
              PkgSig bundle bridgeRoute pkg := by
  intro window bridgeRouteRow bridgePkg
  obtain ⟨_prefixUnary, _lowerUnary, _upperUnary, _widthUnary, _inclusionUnary, _scheduleUnary,
    regReadUnary, _provenanceUnary, certUnary, lowerUpperRow, widthInclusionRow,
    _regReadPkg⟩ := window
  have bridgeUnary : UnaryHistory bridgeRoute :=
    unary_cont_closed regReadUnary certUnary bridgeRouteRow
  exact
    ⟨bridgeUnary, lowerUpperRow, widthInclusionRow, bridgeRouteRow, bridgePkg⟩

theorem NestedIntervalFiniteCarrier_real_seal_boundary [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
        endpoint pkgLedger bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
            endpoint pkgLedger bundle pkg ∧
            (hsame row sealFace ∨ hsame row regRead ∨ hsame row endpoint ∨
              hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
            endpoint pkgLedger bundle pkg ∧
            (hsame row sealFace ∨ hsame row regRead ∨ hsame row endpoint ∨
              hsame row pkgLedger))
        (fun row : BHist =>
          NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
            endpoint pkgLedger bundle pkg ∧
            (hsame row sealFace ∨ hsame row regRead ∨ hsame row endpoint ∨
              hsame row pkgLedger))
        hsame := by
  intro carrier
  let SealSurface : BHist -> Prop :=
    fun row : BHist =>
      NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace
        endpoint pkgLedger bundle pkg ∧
        (hsame row sealFace ∨ hsame row regRead ∨ hsame row endpoint ∨ hsame row pkgLedger)
  have sealSource : SealSurface sealFace :=
    And.intro carrier (Or.inl (hsame_refl sealFace))
  have transportSurface :
      forall {row row' : BHist}, hsame row row' -> SealSurface row -> SealSurface row' := by
    intro row row' sameRow sourceRow
    have rowFromRow' : hsame row' row :=
      hsame_symm sameRow
    cases sourceRow.right with
    | inl sameSeal =>
        exact And.intro sourceRow.left (Or.inl (hsame_trans rowFromRow' sameSeal))
    | inr rest =>
        cases rest with
        | inl sameRegRead =>
            exact And.intro sourceRow.left (Or.inr (Or.inl (hsame_trans rowFromRow' sameRegRead)))
        | inr rest' =>
            cases rest' with
            | inl sameEndpoint =>
                exact
                  And.intro sourceRow.left
                    (Or.inr (Or.inr (Or.inl (hsame_trans rowFromRow' sameEndpoint))))
            | inr samePkgLedger =>
                exact
                  And.intro sourceRow.left
                    (Or.inr (Or.inr (Or.inr (hsame_trans rowFromRow' samePkgLedger))))
  exact {
    core := {
      carrier_inhabited := Exists.intro sealFace sealSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameRow sameRow'
        exact hsame_trans sameRow sameRow'
      carrier_respects_equiv := by
        intro row row' same sourceRow
        exact transportSurface same sourceRow
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem NestedIntervalFiniteCarrier_public_window_boundary [AskSetup] [PackageSetup]
    {lower upper order width inclusion schedule regRead sealFace endpoint pkgLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NestedIntervalFiniteCarrier lower upper order width inclusion schedule regRead sealFace endpoint
        pkgLedger bundle pkg ->
      NestedIntervalRegSeqRatWindow schedule lower upper width inclusion schedule regRead pkgLedger
        endpoint bundle pkg ->
        UnaryHistory lower ∧ UnaryHistory upper ∧ UnaryHistory width ∧
          UnaryHistory inclusion ∧ UnaryHistory schedule ∧ UnaryHistory regRead ∧
            UnaryHistory sealFace ∧ Cont lower upper endpoint ∧ Cont lower upper width ∧
              Cont width inclusion regRead ∧ PkgSig bundle pkgLedger pkg ∧
                PkgSig bundle regRead pkg := by
  intro carrier window
  obtain ⟨lowerUnary, upperUnary, _orderUnary, widthUnary, inclusionUnary, scheduleUnary,
    regReadUnary, sealFaceUnary, _endpointUnary, _pkgLedgerUnary, endpointRow, _ledgerRow,
    ledgerPkg⟩ := carrier
  obtain ⟨_prefixUnary, _windowLowerUnary, _windowUpperUnary, _windowWidthUnary,
    _windowInclusionUnary, _windowScheduleUnary, _windowRegReadUnary, _provenanceUnary,
    _certUnary, widthRow, regReadRow, regReadPkg⟩ := window
  exact
    ⟨lowerUnary, upperUnary, widthUnary, inclusionUnary, scheduleUnary, regReadUnary,
      sealFaceUnary, endpointRow, widthRow, regReadRow, ledgerPkg, regReadPkg⟩

end BEDC.Derived.NestedIntervalUp
