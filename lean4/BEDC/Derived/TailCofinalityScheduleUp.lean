import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TailCofinalityScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TailCofinalityScheduleCarrier [AskSetup] [PackageSetup]
    (precision window dyadic regseq sealRow transport route provenance localCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
    UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
        UnaryHistory endpoint ∧ Cont precision window dyadic ∧
          Cont dyadic regseq sealRow ∧ Cont sealRow transport route ∧
            Cont route provenance endpoint ∧ hsame endpoint (append provenance localCert) ∧
              PkgSig bundle endpoint pkg

theorem TailCofinalityScheduleCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
      provenance localCert endpoint bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
            provenance localCert endpoint bundle pkg ∧ hsame row endpoint)
        (fun row : BHist => hsame row endpoint)
        (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert
  intro carrier
  have carrierSource := carrier
  obtain ⟨_precisionUnary, _windowUnary, _dyadicUnary, _regseqUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _precisionWindowRoute, _dyadicRegseqRoute, _sealTransportRoute,
    _routeProvenanceRoute, _endpointLocalCert, endpointPkg⟩ := carrier
  have sourceEndpoint :
      (fun row : BHist =>
        TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
          provenance localCert endpoint bundle pkg ∧ hsame row endpoint) endpoint := by
    exact And.intro carrierSource (hsame_refl endpoint)
  exact {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row other same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source.right
    ledger_sound := by
      intro _row source
      exact And.intro source.right endpointPkg
  }

theorem TailCofinalityScheduleCarrier_diagonal_handoff [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert
      endpoint diagonalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      Cont precision endpoint diagonalRead →
        PkgSig bundle diagonalRead pkg →
          UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
            UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory endpoint ∧
              UnaryHistory diagonalRead ∧ Cont precision window dyadic ∧
                Cont dyadic regseq sealRow ∧ Cont route provenance endpoint ∧
                  Cont precision endpoint diagonalRead ∧ PkgSig bundle endpoint pkg ∧
                    PkgSig bundle diagonalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier precisionEndpointDiagonal diagonalPkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    precisionWindowDyadic, dyadicRegseqSeal, _sealTransportRoute, routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have diagonalUnary : UnaryHistory diagonalRead :=
    unary_cont_closed precisionUnary endpointUnary precisionEndpointDiagonal
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary, endpointUnary,
      diagonalUnary, precisionWindowDyadic, dyadicRegseqSeal, routeProvenanceEndpoint,
      precisionEndpointDiagonal, endpointPkg, diagonalPkg⟩

theorem TailCofinalityScheduleCarrier_window_coverage [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      windowRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      Cont precision window windowRead →
        PkgSig bundle windowRead pkg →
          UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
            UnaryHistory windowRead ∧ Cont precision window dyadic ∧
              Cont precision window windowRead ∧ PkgSig bundle endpoint pkg ∧
                PkgSig bundle windowRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier precisionWindowRead windowReadPkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, _regseqUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed precisionUnary windowUnary precisionWindowRead
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, windowReadUnary, precisionWindowDyadic,
      precisionWindowRead, endpointPkg, windowReadPkg⟩

theorem TailCofinalityScheduleCarrier_threshold_sufficiency [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      thresholdRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      Cont window dyadic thresholdRead →
        PkgSig bundle thresholdRead pkg →
          UnaryHistory window ∧ UnaryHistory dyadic ∧ UnaryHistory regseq ∧
            UnaryHistory thresholdRead ∧ Cont precision window dyadic ∧
              Cont window dyadic thresholdRead ∧ Cont dyadic regseq sealRow ∧
                PkgSig bundle endpoint pkg ∧ PkgSig bundle thresholdRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier windowDyadicThreshold thresholdPkg
  obtain ⟨_precisionUnary, windowUnary, dyadicUnary, regseqUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    precisionWindowDyadic, dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have thresholdUnary : UnaryHistory thresholdRead :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicThreshold
  exact
    ⟨windowUnary, dyadicUnary, regseqUnary, thresholdUnary, precisionWindowDyadic,
      windowDyadicThreshold, dyadicRegseqSeal, endpointPkg, thresholdPkg⟩

theorem TailCofinalityScheduleCarrier_real_seal_readback [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      Cont regseq sealRow sealRead →
        PkgSig bundle sealRead pkg →
          UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
            UnaryHistory regseq ∧ UnaryHistory sealRow ∧ UnaryHistory transport ∧
              UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
                UnaryHistory endpoint ∧ UnaryHistory sealRead ∧ Cont precision window dyadic ∧
                  Cont dyadic regseq sealRow ∧ Cont regseq sealRow sealRead ∧
                    PkgSig bundle endpoint pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier regseqSealRead sealReadPkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    transportUnary, routeUnary, provenanceUnary, localCertUnary, endpointUnary,
    precisionWindowDyadic, dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary sealUnary regseqSealRead
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary, transportUnary,
      routeUnary, provenanceUnary, localCertUnary, endpointUnary, sealReadUnary,
      precisionWindowDyadic, dyadicRegseqSeal, regseqSealRead, endpointPkg, sealReadPkg⟩

theorem TailCofinalityScheduleCarrier_selector_seal_pullback [AskSetup] [PackageSetup]
    {precision budget window dyadic regseq sealRow transport route provenance localCert endpoint
      selectorRead sealRead pullback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      UnaryHistory budget →
        Cont budget window selectorRead →
          Cont selectorRead regseq sealRead →
            Cont sealRead endpoint pullback →
              PkgSig bundle pullback pkg →
                UnaryHistory precision ∧ UnaryHistory budget ∧ UnaryHistory window ∧
                  UnaryHistory regseq ∧ UnaryHistory selectorRead ∧ UnaryHistory sealRead ∧
                    UnaryHistory pullback ∧ Cont precision window dyadic ∧
                      Cont dyadic regseq sealRow ∧ Cont budget window selectorRead ∧
                        Cont selectorRead regseq sealRead ∧ Cont sealRead endpoint pullback ∧
                          PkgSig bundle endpoint pkg ∧ PkgSig bundle pullback pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory
  intro carrier budgetUnary budgetWindowSelector selectorRegseqSeal sealEndpointPullback
    pullbackPkg
  obtain ⟨precisionUnary, windowUnary, _dyadicUnary, regseqUnary, _sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, endpointUnary,
    precisionWindowDyadic, dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed budgetUnary windowUnary budgetWindowSelector
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed selectorUnary regseqUnary selectorRegseqSeal
  have pullbackUnary : UnaryHistory pullback :=
    unary_cont_closed sealReadUnary endpointUnary sealEndpointPullback
  exact
    ⟨precisionUnary, budgetUnary, windowUnary, regseqUnary, selectorUnary, sealReadUnary,
      pullbackUnary, precisionWindowDyadic, dyadicRegseqSeal, budgetWindowSelector,
      selectorRegseqSeal, sealEndpointPullback, endpointPkg, pullbackPkg⟩

theorem TailCofinalityScheduleCarrier_transport_determinacy [AskSetup] [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      precision' window' dyadic' regseq' sealRow' transport' route' provenance' localCert'
      endpoint' sealRead sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      TailCofinalityScheduleCarrier precision' window' dyadic' regseq' sealRow' transport'
          route' provenance' localCert' endpoint' bundle pkg →
        hsame precision precision' →
          hsame window window' →
            hsame dyadic dyadic' →
              hsame regseq regseq' →
                hsame sealRow sealRow' →
                  Cont regseq sealRow sealRead →
                    Cont regseq' sealRow' sealRead' →
                      PkgSig bundle sealRead pkg →
                        PkgSig bundle sealRead' pkg →
                          hsame sealRead sealRead' ∧ UnaryHistory sealRead ∧
                            UnaryHistory sealRead' ∧ PkgSig bundle endpoint pkg ∧
                              PkgSig bundle endpoint' pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame UnaryHistory
  intro carrier carrier' _samePrecision _sameWindow _sameDyadic sameRegseq sameSealRow
    regseqSealRead regseqSealRead' _sealReadPkg _sealReadPkg'
  obtain ⟨_precisionUnary, _windowUnary, _dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    _precisionWindowDyadic, _dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  obtain ⟨_precisionUnary', _windowUnary', _dyadicUnary', regseqUnary', sealUnary',
    _transportUnary', _routeUnary', _provenanceUnary', _localCertUnary', _endpointUnary',
    _precisionWindowDyadic', _dyadicRegseqSeal', _sealTransportRoute',
    _routeProvenanceEndpoint', _endpointLocalCert', endpointPkg'⟩ := carrier'
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary sealUnary regseqSealRead
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed regseqUnary' sealUnary' regseqSealRead'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameRegseq sameSealRow regseqSealRead regseqSealRead'
  exact ⟨sameSealRead, sealReadUnary, sealReadUnary', endpointPkg, endpointPkg'⟩

theorem TailCofinalityScheduleCarrier_regular_cauchy_tail_meet_handoff [AskSetup]
    [PackageSetup]
    {precision window dyadic regseq sealRow transport route provenance localCert endpoint
      pairedSource pairedWindow modulus sharedThreshold meetRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TailCofinalityScheduleCarrier precision window dyadic regseq sealRow transport route
        provenance localCert endpoint bundle pkg →
      UnaryHistory pairedSource →
        UnaryHistory pairedWindow →
          Cont pairedSource pairedWindow modulus →
            Cont modulus dyadic sharedThreshold →
              Cont sharedThreshold regseq meetRead →
                Cont meetRead sealRow sealRead →
                  PkgSig bundle sealRead pkg →
                    UnaryHistory precision ∧ UnaryHistory window ∧ UnaryHistory dyadic ∧
                      UnaryHistory regseq ∧ UnaryHistory sealRow ∧
                        UnaryHistory pairedSource ∧ UnaryHistory pairedWindow ∧
                          UnaryHistory modulus ∧ UnaryHistory sharedThreshold ∧
                            UnaryHistory meetRead ∧ UnaryHistory sealRead ∧
                              Cont precision window dyadic ∧ Cont dyadic regseq sealRow ∧
                                Cont pairedSource pairedWindow modulus ∧
                                  Cont modulus dyadic sharedThreshold ∧
                                    Cont sharedThreshold regseq meetRead ∧
                                      Cont meetRead sealRow sealRead ∧
                                        PkgSig bundle endpoint pkg ∧
                                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro carrier pairedSourceUnary pairedWindowUnary pairedWindowModulus
    modulusDyadicThreshold thresholdRegseqMeet meetSealRead sealReadPkg
  obtain ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary, _endpointUnary,
    precisionWindowDyadic, dyadicRegseqSeal, _sealTransportRoute, _routeProvenanceEndpoint,
    _endpointLocalCert, endpointPkg⟩ := carrier
  have modulusUnary : UnaryHistory modulus :=
    unary_cont_closed pairedSourceUnary pairedWindowUnary pairedWindowModulus
  have sharedThresholdUnary : UnaryHistory sharedThreshold :=
    unary_cont_closed modulusUnary dyadicUnary modulusDyadicThreshold
  have meetReadUnary : UnaryHistory meetRead :=
    unary_cont_closed sharedThresholdUnary regseqUnary thresholdRegseqMeet
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed meetReadUnary sealUnary meetSealRead
  exact
    ⟨precisionUnary, windowUnary, dyadicUnary, regseqUnary, sealUnary,
      pairedSourceUnary, pairedWindowUnary, modulusUnary, sharedThresholdUnary,
      meetReadUnary, sealReadUnary, precisionWindowDyadic, dyadicRegseqSeal,
      pairedWindowModulus, modulusDyadicThreshold, thresholdRegseqMeet, meetSealRead,
      endpointPkg, sealReadPkg⟩

end BEDC.Derived.TailCofinalityScheduleUp
