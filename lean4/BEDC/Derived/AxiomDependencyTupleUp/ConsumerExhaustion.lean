import BEDC.Derived.AxiomDependencyTupleUp

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomDependencyTupleConsumerExhaustion [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      Cont route localName consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory witness ∧
            UnaryHistory supply ∧
              UnaryHistory route ∧
                UnaryHistory localName ∧
                  UnaryHistory consumer ∧
                    Cont mode witness route ∧
                      Cont route supply localName ∧
                        Cont route localName consumer ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier routeLocalConsumer consumerPkg
  obtain ⟨_modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, routeUnary,
    localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
    provenancePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed routeUnary localNameUnary routeLocalConsumer
  exact
    ⟨witnessUnary, supplyUnary, routeUnary, localNameUnary, consumerUnary, modeWitnessRoute,
      routeSupplyLocalName, routeLocalConsumer, provenancePkg, consumerPkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
