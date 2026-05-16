import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_common_selector_refinement [AskSetup] [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      index windowsU modulusU toleranceU tail sealRow transportsU routesU provenanceU nameU
      selector cauchySeal uniformSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.UniformCauchyCriterionUp.UniformCauchyCriterionPacket index windowsU
          modulusU toleranceU tail sealRow transportsU routesU provenanceU nameU bundle pkg ->
        hsame ledger tail ->
          hsame realSeal sealRow ->
            Cont endpoint realSeal selector ->
              Cont ledger realSeal cauchySeal ->
                Cont tail sealRow uniformSeal ->
                  PkgSig bundle selector pkg ->
                    PkgSig bundle cauchySeal pkg ->
                      PkgSig bundle uniformSeal pkg ->
                        UnaryHistory endpoint ∧ UnaryHistory selector ∧
                          UnaryHistory cauchySeal ∧ UnaryHistory uniformSeal ∧
                            hsame cauchySeal uniformSeal ∧ Cont endpoint realSeal selector ∧
                              Cont ledger realSeal cauchySeal ∧
                                Cont tail sealRow uniformSeal ∧ PkgSig bundle endpoint pkg ∧
                                  PkgSig bundle selector pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier uniformPacket sameLedgerTail sameRealSealSealRow endpointRealSealSelector
    ledgerRealSealCauchySeal tailSealRowUniformSeal selectorPkg _cauchySealPkg _uniformSealPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq, _regseqRealSealTransport,
    _transportLocalCertRoute, _routeProvenanceEndpoint, endpointPkg⟩ := carrier
  obtain ⟨_indexUnary, _windowsUnary, _modulusUUnary, _toleranceUUnary, tailUnary,
    sealRowUnary, _transportsUUnary, _routesUUnary, _provenanceUUnary, _nameUUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _nameUPkg⟩ := uniformPacket
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed endpointUnary realSealUnary endpointRealSealSelector
  have cauchySealUnary : UnaryHistory cauchySeal :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealCauchySeal
  have uniformSealUnary : UnaryHistory uniformSeal :=
    unary_cont_closed tailUnary sealRowUnary tailSealRowUniformSeal
  have sameSeals : hsame cauchySeal uniformSeal :=
    cont_respects_hsame sameLedgerTail sameRealSealSealRow ledgerRealSealCauchySeal
      tailSealRowUniformSeal
  exact
    ⟨endpointUnary, selectorUnary, cauchySealUnary, uniformSealUnary, sameSeals,
      endpointRealSealSelector, ledgerRealSealCauchySeal, tailSealRowUniformSeal, endpointPkg,
      selectorPkg⟩

end BEDC.Derived.CauchyCriterionUp
