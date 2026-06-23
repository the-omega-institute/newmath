import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleBHistRowScope [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg ->
      UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
        UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory localName ∧
          hsame transport transport ∧ Cont mode witness route ∧
            Cont route supply localName ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier
  obtain ⟨_modeCases, modeUnary, witnessUnary, supplyUnary, transportUnary,
    routeUnary, localNameUnary, transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  exact
    ⟨modeUnary, witnessUnary, supplyUnary, transportUnary, routeUnary, localNameUnary,
      transportSame, modeWitnessRoute, routeSupplyLocalName, provenancePkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
