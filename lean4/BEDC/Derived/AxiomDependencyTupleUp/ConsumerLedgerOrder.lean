import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleConsumerLedgerOrder [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName modeWitness witnessSupply : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont mode witness modeWitness →
        Cont modeWitness supply witnessSupply →
          PkgSig bundle witnessSupply pkg →
            UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
              UnaryHistory modeWitness ∧ UnaryHistory witnessSupply ∧
                Cont mode witness modeWitness ∧ Cont modeWitness supply witnessSupply ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle witnessSupply pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier modeWitnessRoute witnessSupplyRoute witnessSupplyPkg
  obtain
    ⟨_modeCases, modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
      _localNameUnary, _transportSame, _modeWitnessRoute, _routeSupplyLocalName,
      provenancePkg⟩ := carrier
  have modeWitnessUnary : UnaryHistory modeWitness :=
    unary_cont_closed modeUnary witnessUnary modeWitnessRoute
  have witnessSupplyUnary : UnaryHistory witnessSupply :=
    unary_cont_closed modeWitnessUnary supplyUnary witnessSupplyRoute
  exact
    ⟨modeUnary, witnessUnary, supplyUnary, modeWitnessUnary, witnessSupplyUnary,
      modeWitnessRoute, witnessSupplyRoute, provenancePkg, witnessSupplyPkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
