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

theorem AxiomDependencyMapQueryLedgerFactorization [AskSetup] [PackageSetup]
    {claim mode witness supply transport replay provenance localName ledgerRoute familyRoute
      compilerRoute weaveRoute : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyMapCertificate claim mode witness supply transport replay provenance localName
        bundle pkg →
      Cont supply provenance ledgerRoute →
        Cont supply provenance familyRoute →
          Cont supply provenance compilerRoute →
            Cont supply provenance weaveRoute →
              UnaryHistory ledgerRoute ∧ UnaryHistory familyRoute ∧
                UnaryHistory compilerRoute ∧ UnaryHistory weaveRoute ∧
                  PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro certificate ledgerCont familyCont compilerCont weaveCont
  rcases certificate with
    ⟨_claimUnary, _modeUnary, _witnessUnary, supplyUnary, _transportUnary, _replayUnary,
      provenanceUnary, _localNameUnary, _claimModeWitness, _witnessSupplyTransport,
      _transportReplayProvenance, provenancePkg⟩
  have ledgerUnary : UnaryHistory ledgerRoute :=
    unary_cont_closed supplyUnary provenanceUnary ledgerCont
  have familyUnary : UnaryHistory familyRoute :=
    unary_cont_closed supplyUnary provenanceUnary familyCont
  have compilerUnary : UnaryHistory compilerRoute :=
    unary_cont_closed supplyUnary provenanceUnary compilerCont
  have weaveUnary : UnaryHistory weaveRoute :=
    unary_cont_closed supplyUnary provenanceUnary weaveCont
  exact ⟨ledgerUnary, familyUnary, compilerUnary, weaveUnary, provenancePkg⟩

end BEDC.Derived.AxiomDependencyMapUp
