import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxiomDependencyMapUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxiomDependencyMapCertificate [AskSetup] [PackageSetup]
    (claim mode witness supply transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory claim ∧ UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
    UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
      UnaryHistory localName ∧ Cont claim mode witness ∧ Cont witness supply transport ∧
        Cont transport replay provenance ∧ PkgSig bundle provenance pkg

theorem AxiomDependencyMapModeSoundness [AskSetup] [PackageSetup]
    {claim mode witness supply transport replay provenance localName modeWitnessRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyMapCertificate claim mode witness supply transport replay provenance localName
        bundle pkg →
      Cont mode witness modeWitnessRoute →
        UnaryHistory claim ∧ UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
          UnaryHistory modeWitnessRoute ∧ Cont mode witness modeWitnessRoute ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro certificate modeWitnessCont
  rcases certificate with
    ⟨claimUnary, modeUnary, witnessUnary, supplyUnary, _transportUnary, _replayUnary,
      _provenanceUnary, _localNameUnary, _claimModeWitness, _witnessSupplyTransport,
      _transportReplayProvenance, provenancePkg⟩
  have routeUnary : UnaryHistory modeWitnessRoute :=
    unary_cont_closed modeUnary witnessUnary modeWitnessCont
  exact
    ⟨claimUnary, modeUnary, witnessUnary, supplyUnary, routeUnary, modeWitnessCont,
      provenancePkg⟩

theorem AxiomDependencyMapRequiredSupplySeparation [AskSetup] [PackageSetup]
    {claim mode witness supply transport replay provenance localName supplyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyMapCertificate claim mode witness supply transport replay provenance localName
        bundle pkg →
      Cont supply transport supplyRead →
        PkgSig bundle supplyRead pkg →
          UnaryHistory claim ∧ UnaryHistory mode ∧ UnaryHistory witness ∧
            UnaryHistory supply ∧ UnaryHistory transport ∧ UnaryHistory supplyRead ∧
              Cont supply transport supplyRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle supplyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro certificate supplyTransportRead supplyReadPkg
  rcases certificate with
    ⟨claimUnary, modeUnary, witnessUnary, supplyUnary, transportUnary, _replayUnary,
      _provenanceUnary, _localNameUnary, _claimModeWitness, _witnessSupplyTransport,
      _transportReplayProvenance, provenancePkg⟩
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed supplyUnary transportUnary supplyTransportRead
  exact
    ⟨claimUnary, modeUnary, witnessUnary, supplyUnary, transportUnary, supplyReadUnary,
      supplyTransportRead, provenancePkg, supplyReadPkg⟩

theorem AxiomDependencyMapCertificate_query_ledger_factorization [AskSetup] [PackageSetup]
    {claim mode witness supply transport replay provenance localName modeRead supplyRead
      ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyMapCertificate claim mode witness supply transport replay provenance
        localName bundle pkg →
      Cont claim mode modeRead →
        Cont modeRead witness supplyRead →
          Cont supplyRead provenance ledgerRead →
            PkgSig bundle ledgerRead pkg →
              UnaryHistory claim ∧ UnaryHistory mode ∧ UnaryHistory witness ∧
                UnaryHistory supply ∧ UnaryHistory provenance ∧ UnaryHistory modeRead ∧
                  UnaryHistory supplyRead ∧ UnaryHistory ledgerRead ∧
                    Cont claim mode witness ∧ Cont witness supply transport ∧
                      Cont transport replay provenance ∧ Cont claim mode modeRead ∧
                        Cont modeRead witness supplyRead ∧
                          Cont supplyRead provenance ledgerRead ∧
                            PkgSig bundle provenance pkg ∧ PkgSig bundle ledgerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro certificate claimModeRead modeReadWitnessSupply supplyProvenanceLedger ledgerPkg
  obtain ⟨claimUnary, modeUnary, witnessUnary, supplyUnary, _transportUnary, _replayUnary,
    provenanceUnary, _localNameUnary, claimModeWitness, witnessSupplyTransport,
      transportReplayProvenance, provenancePkg⟩ := certificate
  have modeReadUnary : UnaryHistory modeRead :=
    unary_cont_closed claimUnary modeUnary claimModeRead
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed modeReadUnary witnessUnary modeReadWitnessSupply
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed supplyReadUnary provenanceUnary supplyProvenanceLedger
  exact
    ⟨claimUnary, modeUnary, witnessUnary, supplyUnary, provenanceUnary, modeReadUnary,
      supplyReadUnary, ledgerReadUnary, claimModeWitness, witnessSupplyTransport,
        transportReplayProvenance, claimModeRead, modeReadWitnessSupply,
          supplyProvenanceLedger, provenancePkg, ledgerPkg⟩

end BEDC.Derived.AxiomDependencyMapUp
