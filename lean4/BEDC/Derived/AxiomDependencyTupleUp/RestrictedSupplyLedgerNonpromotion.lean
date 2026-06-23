import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleRestrictedSupplyLedgerNonpromotion [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont witness supply consumer →
        PkgSig bundle provenance pkg →
          UnaryHistory witness ∧ UnaryHistory supply ∧ Cont witness supply consumer ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier witnessSupplyConsumer provenancePkg
  obtain ⟨_modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    _localNameUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocalName,
    _carrierPkg⟩ := carrier
  exact ⟨witnessUnary, supplyUnary, witnessSupplyConsumer, provenancePkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
