import BEDC.Derived.RatUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ApartnessRealUp

open BEDC.Derived.RatUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ApartnessRealCarrier [AskSetup] [PackageSetup]
    (left right radius window leftReadback rightReadback ledger provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory radius ∧ UnaryHistory window ∧
    UnaryHistory leftReadback ∧ UnaryHistory rightReadback ∧ UnaryHistory ledger ∧
      UnaryHistory provenance ∧ UnaryHistory endpoint ∧ Cont left window leftReadback ∧
        Cont right window rightReadback ∧ Cont left right endpoint ∧
          Cont leftReadback rightReadback ledger ∧ PkgSig bundle endpoint pkg

theorem ApartnessRealCarrier_symmetry_stability [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback ledger swappedLedger provenance endpoint
      swappedEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealCarrier left right radius window leftReadback rightReadback ledger provenance
        endpoint bundle pkg ->
      Cont right left swappedEndpoint -> Cont rightReadback leftReadback swappedLedger ->
        PkgSig bundle swappedEndpoint pkg ->
          ApartnessRealCarrier right left radius window rightReadback leftReadback swappedLedger
              provenance swappedEndpoint bundle pkg ∧
            hsame radius radius ∧ Cont rightReadback leftReadback swappedLedger := by
  intro carrier swappedEndpointRow swappedLedgerRow swappedPkg
  have swappedEndpointUnary : UnaryHistory swappedEndpoint :=
    unary_cont_closed carrier.right.left carrier.left swappedEndpointRow
  have swappedLedgerUnary : UnaryHistory swappedLedger :=
    unary_cont_closed carrier.right.right.right.right.right.left
      carrier.right.right.right.right.left swappedLedgerRow
  constructor
  · constructor
    · exact carrier.right.left
    · constructor
      · exact carrier.left
      · constructor
        · exact carrier.right.right.left
        · constructor
          · exact carrier.right.right.right.left
          · constructor
            · exact carrier.right.right.right.right.right.left
            · constructor
              · exact carrier.right.right.right.right.left
              · constructor
                · exact swappedLedgerUnary
                · constructor
                  · exact carrier.right.right.right.right.right.right.right.left
                  · constructor
                    · exact swappedEndpointUnary
                    · constructor
                      · exact carrier.right.right.right.right.right.right.right.right.right.right.left
                      · constructor
                        · exact carrier.right.right.right.right.right.right.right.right.right.left
                        · constructor
                          · exact swappedEndpointRow
                          · constructor
                            · exact swappedLedgerRow
                            · exact swappedPkg
  · constructor
    · exact hsame_refl radius
    · exact swappedLedgerRow

theorem ApartnessRealNameCertObligationSurface_rows [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback ledger swappedLedger provenance endpoint
      swappedEndpoint metricEndpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealCarrier left right radius window leftReadback rightReadback ledger provenance
        endpoint bundle pkg ->
      Cont right left swappedEndpoint -> Cont rightReadback leftReadback swappedLedger ->
        PkgSig bundle swappedEndpoint pkg -> Cont ledger provenance metricEndpoint ->
          PkgSig bundle metricEndpoint pkg ->
            ApartnessRealCarrier right left radius window rightReadback leftReadback swappedLedger
                provenance swappedEndpoint bundle pkg ∧
              hsame radius radius ∧ Cont rightReadback leftReadback swappedLedger ∧
                UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory radius ∧
                  UnaryHistory window ∧ UnaryHistory leftReadback ∧
                    UnaryHistory rightReadback ∧ UnaryHistory ledger ∧
                      UnaryHistory metricEndpoint ∧ Cont leftReadback rightReadback ledger ∧
                        Cont ledger provenance metricEndpoint ∧ PkgSig bundle metricEndpoint pkg := by
  intro carrier swappedEndpointRow swappedLedgerRow swappedEndpointSig metricEndpointRow
    metricEndpointSig
  have symmetryData :=
    ApartnessRealCarrier_symmetry_stability carrier swappedEndpointRow swappedLedgerRow
      swappedEndpointSig
  obtain ⟨leftUnary, rightUnary, radiusUnary, windowUnary, leftReadbackUnary,
    rightReadbackUnary, ledgerUnary, provenanceUnary, _endpointUnary, _leftWindowReadback,
    _rightWindowReadback, _endpointRow, ledgerRow, _endpointSig⟩ := carrier
  have metricEndpointUnary : UnaryHistory metricEndpoint :=
    unary_cont_closed ledgerUnary provenanceUnary metricEndpointRow
  exact
    ⟨symmetryData.left,
      symmetryData.right.left,
      symmetryData.right.right,
      leftUnary,
      rightUnary,
      radiusUnary,
      windowUnary,
      leftReadbackUnary,
      rightReadbackUnary,
      ledgerUnary,
      metricEndpointUnary,
      ledgerRow,
      metricEndpointRow,
      metricEndpointSig⟩

theorem ApartnessRealCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback ledger provenance endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealCarrier left right radius window leftReadback rightReadback ledger provenance
        endpoint bundle pkg ->
      UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory radius ∧ UnaryHistory window ∧
        UnaryHistory leftReadback ∧ UnaryHistory rightReadback ∧ UnaryHistory ledger ∧
          UnaryHistory endpoint ∧ Cont left window leftReadback ∧
            Cont right window rightReadback ∧ Cont left right endpoint ∧
              Cont leftReadback rightReadback ledger ∧
                hsame leftReadback (append left window) ∧
                  hsame rightReadback (append right window) ∧
                    hsame endpoint (append left right) ∧
                      hsame ledger (append leftReadback rightReadback) ∧
                        PkgSig bundle endpoint pkg := by
  intro carrier
  obtain ⟨leftUnary, rightUnary, radiusUnary, windowUnary, leftReadbackUnary,
    rightReadbackUnary, ledgerUnary, _provenanceUnary, endpointUnary, leftReadbackRow,
    rightReadbackRow, endpointRow, ledgerRow, endpointSig⟩ := carrier
  exact
    ⟨leftUnary, rightUnary, radiusUnary, windowUnary, leftReadbackUnary, rightReadbackUnary,
      ledgerUnary, endpointUnary, leftReadbackRow, rightReadbackRow, endpointRow, ledgerRow,
      leftReadbackRow, rightReadbackRow, endpointRow, ledgerRow, endpointSig⟩

theorem ApartnessRealCarrier_metric_consumer_separation_boundary [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback ledger provenance endpoint consumer :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealCarrier left right radius window leftReadback rightReadback ledger provenance
        endpoint bundle pkg ->
      Cont ledger provenance consumer ->
        PkgSig bundle consumer pkg ->
          UnaryHistory leftReadback ∧ UnaryHistory rightReadback ∧ UnaryHistory ledger ∧
            UnaryHistory endpoint ∧ UnaryHistory consumer ∧
              Cont leftReadback rightReadback ledger ∧ Cont left right endpoint ∧
                Cont ledger provenance consumer ∧ PkgSig bundle consumer pkg := by
  intro carrier consumerRow consumerSig
  obtain ⟨_leftUnary, _rightUnary, _radiusUnary, _windowUnary, leftReadbackUnary,
    rightReadbackUnary, ledgerUnary, provenanceUnary, endpointUnary, _leftWindowReadback,
    _rightWindowReadback, leftRightEndpoint, leftReadbackRightReadbackLedger,
    _endpointSig⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed ledgerUnary provenanceUnary consumerRow
  exact
    ⟨leftReadbackUnary, rightReadbackUnary, ledgerUnary, endpointUnary, consumerUnary,
      leftReadbackRightReadbackLedger, leftRightEndpoint, consumerRow, consumerSig⟩

def ApartnessRealSeparationPacket [AskSetup] [PackageSetup]
    (left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  PositiveUnaryDenominator radius ∧ Cont left window leftEndpoint ∧
    Cont right window rightEndpoint ∧ Cont leftEndpoint rightEndpoint forwardLedger ∧
      Cont rightEndpoint leftEndpoint reverseLedger ∧
        Cont forwardLedger reverseLedger pkgrow ∧
          Cont reverseLedger forwardLedger pkgrow ∧ PkgSig bundle pkgrow pkg

theorem ApartnessRealSeparationPacket_symmetry_stability [AskSetup] [PackageSetup]
    {left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealSeparationPacket left right radius window leftEndpoint rightEndpoint
        forwardLedger reverseLedger pkgrow bundle pkg ->
      ApartnessRealSeparationPacket right left radius window rightEndpoint leftEndpoint
          reverseLedger forwardLedger pkgrow bundle pkg ∧
        hsame radius radius ∧ hsame window window := by
  intro packet
  exact
    And.intro
      (And.intro packet.left
        (And.intro packet.right.right.left
          (And.intro packet.right.left
            (And.intro packet.right.right.right.right.left
              (And.intro packet.right.right.right.left
                  (And.intro packet.right.right.right.right.right.right.left
                    (And.intro packet.right.right.right.right.right.left
                      packet.right.right.right.right.right.right.right)))))))
      (And.intro (hsame_refl radius) (hsame_refl window))

theorem ApartnessRealSeparationPacket_real_separation_scope [AskSetup] [PackageSetup]
    {left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow
      scopeRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealSeparationPacket left right radius window leftEndpoint rightEndpoint
        forwardLedger reverseLedger pkgrow bundle pkg ->
      Cont pkgrow window scopeRow ->
        PkgSig bundle scopeRow pkg ->
          PositiveUnaryDenominator radius ∧ Cont left window leftEndpoint ∧
            Cont right window rightEndpoint ∧
              Cont leftEndpoint rightEndpoint forwardLedger ∧
                Cont rightEndpoint leftEndpoint reverseLedger ∧
                  Cont forwardLedger reverseLedger pkgrow ∧
                    Cont reverseLedger forwardLedger pkgrow ∧
                      Cont pkgrow window scopeRow ∧ PkgSig bundle scopeRow pkg := by
  intro packet scopeCont scopePkg
  obtain ⟨positiveRadius, leftEndpointRow, rightEndpointRow, forwardLedgerRow,
    reverseLedgerRow, forwardPkgRow, reversePkgRow, _pkgSig⟩ := packet
  exact
    And.intro positiveRadius
      (And.intro leftEndpointRow
        (And.intro rightEndpointRow
          (And.intro forwardLedgerRow
            (And.intro reverseLedgerRow
              (And.intro forwardPkgRow
                (And.intro reversePkgRow
                  (And.intro scopeCont scopePkg)))))))

theorem ApartnessRealSeparationPacket_metric_handoff [AskSetup] [PackageSetup]
    {leftName rightName radius window leftEndpoint rightEndpoint separation metricRow endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory leftName ->
    UnaryHistory rightName ->
    UnaryHistory radius ->
    UnaryHistory window ->
    UnaryHistory metricRow ->
    Cont leftName rightName leftEndpoint ->
    Cont radius window rightEndpoint ->
    Cont leftEndpoint rightEndpoint separation ->
    Cont separation metricRow endpoint ->
    PkgSig bundle endpoint pkg ->
      UnaryHistory leftEndpoint ∧ UnaryHistory rightEndpoint ∧ UnaryHistory separation ∧
        UnaryHistory endpoint ∧ hsame separation (append leftEndpoint rightEndpoint) ∧
          hsame endpoint (append separation metricRow) ∧ PkgSig bundle endpoint pkg := by
  intro leftUnary rightUnary radiusUnary windowUnary metricUnary leftEndpointRow rightEndpointRow
    separationRow endpointRow pkgSig
  have leftEndpointUnary : UnaryHistory leftEndpoint :=
    unary_cont_closed leftUnary rightUnary leftEndpointRow
  have rightEndpointUnary : UnaryHistory rightEndpoint :=
    unary_cont_closed radiusUnary windowUnary rightEndpointRow
  have separationUnary : UnaryHistory separation :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary separationRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed separationUnary metricUnary endpointRow
  exact And.intro leftEndpointUnary
    (And.intro rightEndpointUnary
      (And.intro separationUnary
        (And.intro endpointUnary
          (And.intro separationRow
            (And.intro endpointRow pkgSig)))))

def ApartnessRealMetricHandoffPacket [AskSetup] [PackageSetup]
    (left right radius window leftReadback rightReadback separation provenance endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory radius ∧ UnaryHistory window ∧
    UnaryHistory provenance ∧ Cont left window leftReadback ∧
      Cont right window rightReadback ∧ Cont leftReadback rightReadback separation ∧
        Cont separation provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ApartnessRealMetricHandoffPacket_transport [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback separation provenance endpoint left'
      right' radius' window' leftReadback' rightReadback' separation' provenance'
      endpoint' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealMetricHandoffPacket left right radius window leftReadback rightReadback
        separation provenance endpoint bundle pkg ->
      hsame left left' -> hsame right right' -> hsame radius radius' ->
        hsame window window' -> hsame provenance provenance' ->
          Cont left' window' leftReadback' -> Cont right' window' rightReadback' ->
            Cont leftReadback' rightReadback' separation' ->
              Cont separation' provenance' endpoint' -> PkgSig bundle endpoint' pkg ->
                ApartnessRealMetricHandoffPacket left' right' radius' window' leftReadback'
                    rightReadback' separation' provenance' endpoint' bundle pkg ∧
                  hsame leftReadback leftReadback' ∧ hsame rightReadback rightReadback' ∧
                    hsame separation separation' ∧ hsame endpoint endpoint' := by
  intro packet sameLeft sameRight sameRadius sameWindow sameProvenance
  intro leftRow' rightRow' separationRow' endpointRow' pkgSig'
  have sameLeftReadback : hsame leftReadback leftReadback' :=
    cont_respects_hsame sameLeft sameWindow
      packet.right.right.right.right.right.left leftRow'
  have sameRightReadback : hsame rightReadback rightReadback' :=
    cont_respects_hsame sameRight sameWindow
      packet.right.right.right.right.right.right.left rightRow'
  have sameSeparation : hsame separation separation' :=
    cont_respects_hsame sameLeftReadback sameRightReadback
      packet.right.right.right.right.right.right.right.left separationRow'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameSeparation sameProvenance
      packet.right.right.right.right.right.right.right.right.left endpointRow'
  have transported :
      ApartnessRealMetricHandoffPacket left' right' radius' window' leftReadback'
          rightReadback' separation' provenance' endpoint' bundle pkg :=
    ⟨unary_transport packet.left sameLeft,
      unary_transport packet.right.left sameRight,
      unary_transport packet.right.right.left sameRadius,
      unary_transport packet.right.right.right.left sameWindow,
      unary_transport packet.right.right.right.right.left sameProvenance,
      leftRow',
      rightRow',
      separationRow',
      endpointRow',
      pkgSig'⟩
  exact ⟨transported, sameLeftReadback, sameRightReadback, sameSeparation, sameEndpoint⟩

theorem ApartnessRealMetricHandoffPacket_metric_consumer_separation_boundary
    [AskSetup] [PackageSetup]
    {left right radius window leftReadback rightReadback separation provenance endpoint
      consumerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealMetricHandoffPacket left right radius window leftReadback rightReadback
        separation provenance endpoint bundle pkg ->
      Cont endpoint window consumerRow ->
        PkgSig bundle consumerRow pkg ->
          UnaryHistory left ∧ UnaryHistory right ∧ UnaryHistory radius ∧ UnaryHistory window ∧
            UnaryHistory leftReadback ∧ UnaryHistory rightReadback ∧
              UnaryHistory separation ∧ UnaryHistory endpoint ∧ UnaryHistory consumerRow ∧
                Cont left window leftReadback ∧ Cont right window rightReadback ∧
                  Cont leftReadback rightReadback separation ∧
                    Cont separation provenance endpoint ∧
                      hsame consumerRow (append endpoint window) ∧
                        PkgSig bundle consumerRow pkg := by
  intro packet consumerRowRow consumerPkg
  have leftReadbackUnary : UnaryHistory leftReadback :=
    unary_cont_closed packet.left packet.right.right.right.left
      packet.right.right.right.right.right.left
  have rightReadbackUnary : UnaryHistory rightReadback :=
    unary_cont_closed packet.right.left packet.right.right.right.left
      packet.right.right.right.right.right.right.left
  have separationUnary : UnaryHistory separation :=
    unary_cont_closed leftReadbackUnary rightReadbackUnary
      packet.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed separationUnary packet.right.right.right.right.left
      packet.right.right.right.right.right.right.right.right.left
  have consumerUnary : UnaryHistory consumerRow :=
    unary_cont_closed endpointUnary packet.right.right.right.left consumerRowRow
  exact
    ⟨packet.left,
      packet.right.left,
      packet.right.right.left,
      packet.right.right.right.left,
      leftReadbackUnary,
      rightReadbackUnary,
      separationUnary,
      endpointUnary,
      consumerUnary,
      packet.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right.left,
      consumerRowRow,
      consumerPkg⟩

theorem ApartnessRealSeparationPacket_finite_window_transport [AskSetup] [PackageSetup]
    {left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow left'
      right' radius' window' leftEndpoint' rightEndpoint' forwardLedger' reverseLedger' pkgrow' :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealSeparationPacket left right radius window leftEndpoint rightEndpoint forwardLedger
        reverseLedger pkgrow bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          PositiveUnaryDenominator radius' ->
            hsame window window' ->
              Cont left' window' leftEndpoint' ->
                Cont right' window' rightEndpoint' ->
                  Cont leftEndpoint' rightEndpoint' forwardLedger' ->
                    Cont rightEndpoint' leftEndpoint' reverseLedger' ->
                      Cont forwardLedger' reverseLedger' pkgrow' ->
                        Cont reverseLedger' forwardLedger' pkgrow' ->
                          PkgSig bundle pkgrow' pkg ->
                            ApartnessRealSeparationPacket left' right' radius' window'
                                leftEndpoint' rightEndpoint' forwardLedger' reverseLedger' pkgrow'
                                bundle pkg ∧
                              hsame leftEndpoint leftEndpoint' ∧
                                hsame rightEndpoint rightEndpoint' ∧
                                  hsame forwardLedger forwardLedger' ∧
                                    hsame reverseLedger reverseLedger' := by
  intro packet sameLeft sameRight positiveRadius' sameWindow leftEndpointRow'
    rightEndpointRow' forwardLedgerRow' reverseLedgerRow' pkgForwardRow' pkgReverseRow' pkgSig'
  obtain ⟨_positiveRadius, leftEndpointRow, rightEndpointRow, forwardLedgerRow,
    reverseLedgerRow, _pkgForwardRow, _pkgReverseRow, _pkgSig⟩ := packet
  have sameLeftEndpoint : hsame leftEndpoint leftEndpoint' :=
    cont_respects_hsame sameLeft sameWindow leftEndpointRow leftEndpointRow'
  have sameRightEndpoint : hsame rightEndpoint rightEndpoint' :=
    cont_respects_hsame sameRight sameWindow rightEndpointRow rightEndpointRow'
  have sameForwardLedger : hsame forwardLedger forwardLedger' :=
    cont_respects_hsame sameLeftEndpoint sameRightEndpoint forwardLedgerRow forwardLedgerRow'
  have sameReverseLedger : hsame reverseLedger reverseLedger' :=
    cont_respects_hsame sameRightEndpoint sameLeftEndpoint reverseLedgerRow reverseLedgerRow'
  constructor
  · constructor
    · exact positiveRadius'
    · constructor
      · exact leftEndpointRow'
      · constructor
        · exact rightEndpointRow'
        · constructor
          · exact forwardLedgerRow'
          · constructor
            · exact reverseLedgerRow'
            · constructor
              · exact pkgForwardRow'
              · constructor
                · exact pkgReverseRow'
                · exact pkgSig'
  · constructor
    · exact sameLeftEndpoint
    · constructor
      · exact sameRightEndpoint
      · constructor
        · exact sameForwardLedger
        · exact sameReverseLedger

theorem ApartnessRealSeparationPacket_metric_consumer_separation_boundary [AskSetup]
    [PackageSetup]
    {left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow
      metricRow consumerRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealSeparationPacket left right radius window leftEndpoint rightEndpoint
        forwardLedger reverseLedger pkgrow bundle pkg ->
      UnaryHistory left ->
        UnaryHistory right ->
          UnaryHistory window ->
            UnaryHistory metricRow ->
              Cont pkgrow metricRow consumerRow ->
                PkgSig bundle consumerRow pkg ->
                  PositiveUnaryDenominator radius ∧ UnaryHistory leftEndpoint ∧
                    UnaryHistory rightEndpoint ∧ UnaryHistory forwardLedger ∧
                      UnaryHistory reverseLedger ∧ UnaryHistory pkgrow ∧
                        UnaryHistory consumerRow ∧ Cont leftEndpoint rightEndpoint forwardLedger ∧
                          Cont rightEndpoint leftEndpoint reverseLedger ∧
                            hsame consumerRow (append pkgrow metricRow) ∧
                              PkgSig bundle consumerRow pkg := by
  intro packet leftUnary rightUnary windowUnary metricUnary consumerRowCont consumerPkg
  have positiveRadius : PositiveUnaryDenominator radius :=
    packet.left
  have leftEndpointCont : Cont left window leftEndpoint :=
    packet.right.left
  have rightEndpointCont : Cont right window rightEndpoint :=
    packet.right.right.left
  have forwardLedgerCont : Cont leftEndpoint rightEndpoint forwardLedger :=
    packet.right.right.right.left
  have reverseLedgerCont : Cont rightEndpoint leftEndpoint reverseLedger :=
    packet.right.right.right.right.left
  have pkgrowCont : Cont forwardLedger reverseLedger pkgrow :=
    packet.right.right.right.right.right.left
  have leftEndpointUnary : UnaryHistory leftEndpoint :=
    unary_cont_closed leftUnary windowUnary leftEndpointCont
  have rightEndpointUnary : UnaryHistory rightEndpoint :=
    unary_cont_closed rightUnary windowUnary rightEndpointCont
  have forwardLedgerUnary : UnaryHistory forwardLedger :=
    unary_cont_closed leftEndpointUnary rightEndpointUnary forwardLedgerCont
  have reverseLedgerUnary : UnaryHistory reverseLedger :=
    unary_cont_closed rightEndpointUnary leftEndpointUnary reverseLedgerCont
  have pkgrowUnary : UnaryHistory pkgrow :=
    unary_cont_closed forwardLedgerUnary reverseLedgerUnary pkgrowCont
  have consumerUnary : UnaryHistory consumerRow :=
    unary_cont_closed pkgrowUnary metricUnary consumerRowCont
  exact
    And.intro positiveRadius
      (And.intro leftEndpointUnary
        (And.intro rightEndpointUnary
          (And.intro forwardLedgerUnary
            (And.intro reverseLedgerUnary
              (And.intro pkgrowUnary
                (And.intro consumerUnary
                  (And.intro forwardLedgerCont
                    (And.intro reverseLedgerCont
                      (And.intro consumerRowCont consumerPkg)))))))))

def ApartnessRealPositiveSeparationCarrier [AskSetup] [PackageSetup]
    (leftName rightName radius window leftReadback rightReadback separation provenance
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory radius ∧
    UnaryHistory window ∧ UnaryHistory provenance ∧ Cont leftName radius leftReadback ∧
      Cont rightName window rightReadback ∧ Cont leftReadback rightReadback separation ∧
        Cont separation provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem ApartnessRealPositiveSeparationCarrier_metric_handoff [AskSetup] [PackageSetup]
    {leftName rightName radius window leftReadback rightReadback separation provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealPositiveSeparationCarrier leftName rightName radius window leftReadback
        rightReadback separation provenance endpoint bundle pkg ->
      UnaryHistory leftReadback ∧ UnaryHistory rightReadback ∧ UnaryHistory separation ∧
        hsame separation (append leftReadback rightReadback) ∧ UnaryHistory endpoint ∧
          hsame endpoint (append separation provenance) ∧ PkgSig bundle endpoint pkg := by
  intro carrier
  have leftNameUnary : UnaryHistory leftName :=
    carrier.left
  have rightNameUnary : UnaryHistory rightName :=
    carrier.right.left
  have radiusUnary : UnaryHistory radius :=
    carrier.right.right.left
  have windowUnary : UnaryHistory window :=
    carrier.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    carrier.right.right.right.right.left
  have leftReadbackRow : Cont leftName radius leftReadback :=
    carrier.right.right.right.right.right.left
  have rightReadbackRow : Cont rightName window rightReadback :=
    carrier.right.right.right.right.right.right.left
  have separationRow : Cont leftReadback rightReadback separation :=
    carrier.right.right.right.right.right.right.right.left
  have endpointRow : Cont separation provenance endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have packageBoundary : PkgSig bundle endpoint pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have leftReadbackUnary : UnaryHistory leftReadback :=
    unary_cont_closed leftNameUnary radiusUnary leftReadbackRow
  have rightReadbackUnary : UnaryHistory rightReadback :=
    unary_cont_closed rightNameUnary windowUnary rightReadbackRow
  have separationUnary : UnaryHistory separation :=
    unary_cont_closed leftReadbackUnary rightReadbackUnary separationRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed separationUnary provenanceUnary endpointRow
  exact And.intro leftReadbackUnary
    (And.intro rightReadbackUnary
      (And.intro separationUnary
        (And.intro separationRow
          (And.intro endpointUnary
            (And.intro endpointRow packageBoundary)))))

theorem ApartnessRealSeparationPacket_metric_handoff_transport [AskSetup] [PackageSetup]
    {left right radius window leftEndpoint rightEndpoint forwardLedger reverseLedger pkgrow
      left' right' window' leftEndpoint' rightEndpoint' forwardLedger' reverseLedger'
      pkgrow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApartnessRealSeparationPacket left right radius window leftEndpoint rightEndpoint
        forwardLedger reverseLedger pkgrow bundle pkg ->
      hsame left left' ->
        hsame right right' ->
          hsame window window' ->
            Cont left' window' leftEndpoint' ->
              Cont right' window' rightEndpoint' ->
                Cont leftEndpoint' rightEndpoint' forwardLedger' ->
                  Cont rightEndpoint' leftEndpoint' reverseLedger' ->
                    Cont forwardLedger' reverseLedger' pkgrow' ->
                      Cont reverseLedger' forwardLedger' pkgrow' ->
                        PkgSig bundle pkgrow' pkg ->
                          ApartnessRealSeparationPacket left' right' radius window'
                              leftEndpoint' rightEndpoint' forwardLedger' reverseLedger'
                              pkgrow' bundle pkg ∧
                            hsame leftEndpoint leftEndpoint' ∧
                              hsame rightEndpoint rightEndpoint' ∧
                                hsame forwardLedger forwardLedger' ∧
                                  hsame reverseLedger reverseLedger' := by
  intro packet sameLeft sameRight sameWindow leftEndpointCont' rightEndpointCont'
    forwardLedgerCont' reverseLedgerCont' forwardPkgCont' reversePkgCont' pkgSig'
  have sameLeftEndpoint : hsame leftEndpoint leftEndpoint' :=
    cont_respects_hsame sameLeft sameWindow packet.right.left leftEndpointCont'
  have sameRightEndpoint : hsame rightEndpoint rightEndpoint' :=
    cont_respects_hsame sameRight sameWindow packet.right.right.left rightEndpointCont'
  have sameForwardLedger : hsame forwardLedger forwardLedger' :=
    cont_respects_hsame sameLeftEndpoint sameRightEndpoint packet.right.right.right.left
      forwardLedgerCont'
  have sameReverseLedger : hsame reverseLedger reverseLedger' :=
    cont_respects_hsame sameRightEndpoint sameLeftEndpoint packet.right.right.right.right.left
      reverseLedgerCont'
  exact
    And.intro
      (And.intro packet.left
        (And.intro leftEndpointCont'
          (And.intro rightEndpointCont'
            (And.intro forwardLedgerCont'
              (And.intro reverseLedgerCont'
                (And.intro forwardPkgCont'
                  (And.intro reversePkgCont' pkgSig')))))))
      (And.intro sameLeftEndpoint
        (And.intro sameRightEndpoint
          (And.intro sameForwardLedger sameReverseLedger)))

end BEDC.Derived.ApartnessRealUp
