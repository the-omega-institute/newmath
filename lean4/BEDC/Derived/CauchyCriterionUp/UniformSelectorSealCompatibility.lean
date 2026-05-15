import BEDC.Derived.CauchyCriterionUp
import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.CauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem CauchyCriterionCarrier_uniform_selector_seal_compatibility [AskSetup]
    [PackageSetup]
    {window modulus tolerance ledger regseq realSeal transport route provenance localCert endpoint
      index windowsU modulusU toleranceU tail sealRow transportsU routesU provenanceU nameU
      cauchySeal uniformSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCriterionCarrier window modulus tolerance ledger regseq realSeal transport route
        provenance localCert endpoint bundle pkg ->
      BEDC.Derived.UniformCauchyCriterionUp.UniformCauchyCriterionPacket index windowsU
        modulusU toleranceU tail sealRow transportsU routesU provenanceU nameU bundle pkg ->
        hsame ledger tail -> hsame realSeal sealRow -> Cont ledger realSeal cauchySeal ->
          Cont tail sealRow uniformSeal ->
            PkgSig bundle cauchySeal pkg -> PkgSig bundle uniformSeal pkg ->
              hsame cauchySeal uniformSeal ∧ UnaryHistory cauchySeal ∧
                UnaryHistory uniformSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro carrier uniformPacket sameLedgerTail sameRealSealSealRow ledgerRealSealCauchySeal
    tailSealRowUniformSeal _cauchySealPkg _uniformSealPkg
  obtain ⟨_windowUnary, _modulusUnary, _toleranceUnary, ledgerUnary, _regseqUnary,
    realSealUnary, _transportUnary, _routeUnary, _provenanceUnary, _localCertUnary,
    _endpointUnary, _windowModulusTolerance, _toleranceLedgerRegseq,
    _regseqRealSealTransport, _transportLocalCertRoute, _routeProvenanceEndpoint,
    _endpointPkg⟩ := carrier
  obtain ⟨_indexUnary, _windowsUnary, _modulusUUnary, _toleranceUUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := uniformPacket
  have cauchySealUnary : UnaryHistory cauchySeal :=
    unary_cont_closed ledgerUnary realSealUnary ledgerRealSealCauchySeal
  have uniformSealUnary : UnaryHistory uniformSeal :=
    unary_cont_closed tailUnary sealRowUnary tailSealRowUniformSeal
  have sameSeals : hsame cauchySeal uniformSeal :=
    cont_respects_hsame sameLedgerTail sameRealSealSealRow ledgerRealSealCauchySeal
      tailSealRowUniformSeal
  exact ⟨sameSeals, cauchySealUnary, uniformSealUnary⟩

end BEDC.Derived.CauchyCriterionUp
