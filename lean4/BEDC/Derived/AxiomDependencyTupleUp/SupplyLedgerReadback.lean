import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleSupplyLedgerReadback [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName supplyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont supply witness supplyRead →
        PkgSig bundle supplyRead pkg →
          UnaryHistory supply ∧ UnaryHistory witness ∧ UnaryHistory supplyRead ∧
            Cont mode witness route ∧ Cont route supply localName ∧
              Cont supply witness supplyRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle supplyRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier supplyWitnessRead supplyReadPkg
  obtain ⟨_modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, _routeUnary,
    _localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have supplyReadUnary : UnaryHistory supplyRead :=
    unary_cont_closed supplyUnary witnessUnary supplyWitnessRead
  exact
    ⟨supplyUnary, witnessUnary, supplyReadUnary, modeWitnessRoute, routeSupplyLocalName,
      supplyWitnessRead, provenancePkg, supplyReadPkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
