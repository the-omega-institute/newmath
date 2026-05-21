import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailComparisonUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyTailComparisonCarrier [AskSetup] [PackageSetup]
    (leftName rightName modulus window endpointLedger readback provenance namecert endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧
    UnaryHistory rightName ∧
    UnaryHistory modulus ∧
    UnaryHistory window ∧
    UnaryHistory endpointLedger ∧
    UnaryHistory readback ∧
    UnaryHistory provenance ∧
    UnaryHistory namecert ∧
    UnaryHistory endpoint ∧
    Cont (append leftName rightName) modulus window ∧
    Cont window endpointLedger readback ∧
    hsame endpoint (append readback provenance) ∧
    hsame namecert endpoint ∧
    PkgSig bundle endpoint pkg

theorem CauchyTailComparisonCarrier_tail_stability [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance namecert endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier leftName rightName modulus window endpointLedger readback
      provenance namecert endpoint bundle pkg →
      Cont (append leftName rightName) modulus window ∧
        Cont window endpointLedger readback ∧
          hsame endpoint (append readback provenance) ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  cases carrier with
  | intro _leftUnary rest =>
      cases rest with
      | intro _rightUnary rest =>
          cases rest with
          | intro _modulusUnary rest =>
              cases rest with
              | intro _windowUnary rest =>
                  cases rest with
                  | intro _endpointLedgerUnary rest =>
                      cases rest with
                      | intro _readbackUnary rest =>
                          cases rest with
                          | intro _provenanceUnary rest =>
                              cases rest with
                              | intro _namecertUnary rest =>
                                  cases rest with
                                  | intro _endpointUnary rest =>
                                      cases rest with
                                      | intro commonWindow rest =>
                                          cases rest with
                                          | intro endpointReadback rest =>
                                              cases rest with
                                              | intro endpointSame rest =>
                                                  cases rest with
                                                  | intro _namecertSame pkgSig =>
                                                      exact And.intro commonWindow
                                                        (And.intro endpointReadback
                                                          (And.intro endpointSame pkgSig))

theorem CauchyTailComparisonCarrier_real_completion_handoff [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance namecert endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier leftName rightName modulus window endpointLedger readback
        provenance namecert endpoint bundle pkg →
      UnaryHistory leftName ∧
        UnaryHistory rightName ∧
          UnaryHistory modulus ∧
            UnaryHistory window ∧
              UnaryHistory endpointLedger ∧
                UnaryHistory readback ∧
                  UnaryHistory provenance ∧
                    UnaryHistory namecert ∧
                      Cont (append leftName rightName) modulus window ∧
                        Cont window endpointLedger readback ∧
                          hsame endpoint (append readback provenance) ∧
                            hsame namecert endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier
  obtain ⟨leftUnary, rightUnary, modulusUnary, windowUnary, endpointLedgerUnary,
    readbackUnary, provenanceUnary, namecertUnary, _endpointUnary, commonWindow,
    endpointReadback, endpointSame, namecertSame, pkgSig⟩ := carrier
  exact And.intro leftUnary
    (And.intro rightUnary
      (And.intro modulusUnary
        (And.intro windowUnary
          (And.intro endpointLedgerUnary
            (And.intro readbackUnary
              (And.intro provenanceUnary
                (And.intro namecertUnary
                  (And.intro commonWindow
                    (And.intro endpointReadback
                      (And.intro endpointSame
                        (And.intro namecertSame pkgSig)))))))))))

theorem CauchyTailComparisonCarrier_non_escape_boundary [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance namecert endpoint
      sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier leftName rightName modulus window endpointLedger readback
        provenance namecert endpoint bundle pkg ->
      Cont readback namecert sealRow ->
        UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory modulus ∧
          UnaryHistory window ∧ UnaryHistory endpointLedger ∧ UnaryHistory readback ∧
            UnaryHistory provenance ∧ UnaryHistory namecert ∧ UnaryHistory endpoint ∧
              UnaryHistory sealRow ∧ Cont (append leftName rightName) modulus window ∧
                Cont window endpointLedger readback ∧ Cont readback namecert sealRow ∧
                  hsame endpoint (append readback provenance) ∧ hsame namecert endpoint ∧
                    PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sealRoute
  obtain ⟨leftUnary, rightUnary, modulusUnary, windowUnary, endpointLedgerUnary,
    readbackUnary, provenanceUnary, namecertUnary, endpointUnary, commonWindow,
    endpointReadback, endpointSame, namecertSame, pkgSig⟩ := carrier
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary namecertUnary sealRoute
  exact
    ⟨leftUnary, rightUnary, modulusUnary, windowUnary, endpointLedgerUnary, readbackUnary,
      provenanceUnary, namecertUnary, endpointUnary, sealRowUnary, commonWindow, endpointReadback,
      sealRoute, endpointSame, namecertSame, pkgSig⟩

theorem CauchyTailComparisonCarrier_real_seal_stability [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance namecert endpoint
      leftName' rightName' modulus' window' endpointLedger' readback' provenance' namecert'
      endpoint' sealRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier leftName rightName modulus window endpointLedger readback
        provenance namecert endpoint bundle pkg ->
      hsame leftName leftName' ->
        hsame rightName rightName' ->
          hsame modulus modulus' ->
            hsame window window' ->
              hsame endpointLedger endpointLedger' ->
                hsame readback readback' ->
                  hsame provenance provenance' ->
                    hsame namecert namecert' ->
                      hsame endpoint endpoint' ->
                        Cont readback' namecert' sealRow' ->
                          PkgSig bundle endpoint' pkg ->
                            UnaryHistory leftName' /\ UnaryHistory rightName' /\
                              UnaryHistory modulus' /\ UnaryHistory window' /\
                                UnaryHistory endpointLedger' /\ UnaryHistory readback' /\
                                  UnaryHistory provenance' /\ UnaryHistory namecert' /\
                                    UnaryHistory endpoint' /\ UnaryHistory sealRow' /\
                                      Cont window' endpointLedger' readback' /\
                                        Cont readback' namecert' sealRow' /\
                                          hsame endpoint' (append readback' provenance') /\
                                            hsame namecert' endpoint' /\
                                              PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier sameLeft sameRight sameModulus sameWindow sameEndpointLedger sameReadback
    sameProvenance sameNamecert sameEndpoint sealRoute pkgSig'
  obtain ⟨leftUnary, rightUnary, modulusUnary, windowUnary, endpointLedgerUnary, readbackUnary,
    provenanceUnary, namecertUnary, endpointUnary, _commonWindow, endpointReadback, endpointSame,
    namecertSame, _pkgSig⟩ := carrier
  have leftUnary' : UnaryHistory leftName' :=
    unary_transport leftUnary sameLeft
  have rightUnary' : UnaryHistory rightName' :=
    unary_transport rightUnary sameRight
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport modulusUnary sameModulus
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have endpointLedgerUnary' : UnaryHistory endpointLedger' :=
    unary_transport endpointLedgerUnary sameEndpointLedger
  have readbackUnary' : UnaryHistory readback' :=
    unary_transport readbackUnary sameReadback
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have namecertUnary' : UnaryHistory namecert' :=
    unary_transport namecertUnary sameNamecert
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have endpointReadback' : Cont window' endpointLedger' readback' :=
    cont_hsame_transport sameWindow sameEndpointLedger sameReadback endpointReadback
  have sealUnary' : UnaryHistory sealRow' :=
    unary_cont_closed readbackUnary' namecertUnary' sealRoute
  have endpointSame' : hsame endpoint' (append readback' provenance') := by
    cases sameReadback
    cases sameProvenance
    exact hsame_trans (hsame_symm sameEndpoint) endpointSame
  have namecertSame' : hsame namecert' endpoint' :=
    hsame_trans (hsame_symm sameNamecert) (hsame_trans namecertSame sameEndpoint)
  exact
    ⟨leftUnary', rightUnary', modulusUnary', windowUnary', endpointLedgerUnary', readbackUnary',
      provenanceUnary', namecertUnary', endpointUnary', sealUnary', endpointReadback', sealRoute,
      endpointSame', namecertSame', pkgSig'⟩

theorem CauchyTailComparisonCarrier_standard_bridge_source [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance namecert endpoint
      bridgeSource : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier leftName rightName modulus window endpointLedger readback
        provenance namecert endpoint bundle pkg →
      hsame bridgeSource (append endpoint provenance) →
        hsame bridgeSource (append (append readback provenance) provenance) ∧
          Cont (append leftName rightName) modulus window ∧
            Cont window endpointLedger readback ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier bridgeSourceEndpoint
  obtain ⟨_leftUnary, _rightUnary, _modulusUnary, _windowUnary, _endpointLedgerUnary,
    _readbackUnary, _provenanceUnary, _namecertUnary, _endpointUnary, commonWindow,
    endpointReadback, endpointSame, _namecertSame, pkgSig⟩ := carrier
  have endpointAppendSame :
      hsame (append endpoint provenance) (append (append readback provenance) provenance) :=
    congrArg (fun row => append row provenance) endpointSame
  exact ⟨hsame_trans bridgeSourceEndpoint endpointAppendSame, commonWindow, endpointReadback, pkgSig⟩

def CauchyTailComparisonCommonWindowCarrier [AskSetup] [PackageSetup]
    (leftName rightName modulus window endpointLedger readback provenance nameRow endpoint :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftName ∧ UnaryHistory rightName ∧ UnaryHistory modulus ∧
    UnaryHistory window ∧ UnaryHistory nameRow ∧ Cont modulus window endpointLedger ∧
      Cont endpointLedger readback endpoint ∧ hsame provenance (append leftName rightName) ∧
        PkgSig bundle endpoint pkg

theorem CauchyTailComparisonCommonWindowCarrier_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {leftName rightName modulus window endpointLedger readback provenance nameRow endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCommonWindowCarrier leftName rightName modulus window endpointLedger
        readback provenance nameRow endpoint bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyTailComparisonCommonWindowCarrier leftName rightName modulus window
            endpointLedger readback provenance nameRow endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyTailComparisonCommonWindowCarrier leftName rightName modulus window
            endpointLedger readback provenance nameRow endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          CauchyTailComparisonCommonWindowCarrier leftName rightName modulus window
            endpointLedger readback provenance nameRow endpoint bundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  have carrierSource := carrier
  obtain ⟨_leftUnary, _rightUnary, modulusUnary, windowUnary, _nameUnary,
    modulusWindowLedger, ledgerReadbackEndpoint, _provenanceRows, _endpointPkg⟩ := carrier
  have endpointLedgerUnary : UnaryHistory endpointLedger :=
    unary_cont_closed modulusUnary windowUnary modulusWindowLedger
  have _sameEndpointLedger : Cont endpointLedger readback endpoint := ledgerReadbackEndpoint
  have _endpointLedgerUnary : UnaryHistory endpointLedger := endpointLedgerUnary
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint (And.intro carrierSource (hsame_refl endpoint))
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

theorem CauchyTailComparisonCarrier_window_composition_seal_exhaustion
    [AskSetup] [PackageSetup]
    {leftName middleName rightName modulusXY windowXY endpointLedgerXY readbackXY
      provenanceXY namecertXY endpointXY modulusYZ windowYZ endpointLedgerYZ readbackYZ
      provenanceYZ namecertYZ endpointYZ modulusXZ windowXZ endpointLedgerXZ readbackXZ
      namecertXZ sealRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyTailComparisonCarrier leftName middleName modulusXY windowXY endpointLedgerXY
        readbackXY provenanceXY namecertXY endpointXY bundle pkg ->
      CauchyTailComparisonCarrier middleName rightName modulusYZ windowYZ endpointLedgerYZ
        readbackYZ provenanceYZ namecertYZ endpointYZ bundle pkg ->
        UnaryHistory modulusXZ ->
          UnaryHistory endpointLedgerXZ ->
            UnaryHistory namecertXZ ->
              Cont (append leftName rightName) modulusXZ windowXZ ->
                Cont windowXZ endpointLedgerXZ readbackXZ ->
                  Cont readbackXZ namecertXZ sealRow ->
                    UnaryHistory (append leftName rightName) /\
                      UnaryHistory windowXZ /\
                        UnaryHistory readbackXZ /\ UnaryHistory sealRow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont append
  intro carrierXY carrierYZ modulusUnary endpointLedgerUnary namecertUnary composedWindow
    readbackRoute sealRoute
  obtain ⟨leftUnary, _middleUnaryXY, _modulusXYUnary, _windowXYUnary,
    _endpointLedgerXYUnary, _readbackXYUnary, _provenanceXYUnary, _namecertXYUnary,
    _endpointXYUnary, _commonWindowXY, _endpointReadbackXY, _endpointSameXY,
    _namecertSameXY, _pkgSigXY⟩ := carrierXY
  obtain ⟨_middleUnaryYZ, rightUnary, _modulusYZUnary, _windowYZUnary,
    _endpointLedgerYZUnary, _readbackYZUnary, _provenanceYZUnary, _namecertYZUnary,
    _endpointYZUnary, _commonWindowYZ, _endpointReadbackYZ, _endpointSameYZ,
    _namecertSameYZ, _pkgSigYZ⟩ := carrierYZ
  have endpointNamesUnary : UnaryHistory (append leftName rightName) :=
    unary_append_closed leftUnary rightUnary
  have windowUnary : UnaryHistory windowXZ :=
    unary_cont_closed endpointNamesUnary modulusUnary composedWindow
  have readbackUnary : UnaryHistory readbackXZ :=
    unary_cont_closed windowUnary endpointLedgerUnary readbackRoute
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed readbackUnary namecertUnary sealRoute
  exact And.intro endpointNamesUnary
    (And.intro windowUnary (And.intro readbackUnary sealUnary))

end BEDC.Derived.CauchyTailComparisonUp
