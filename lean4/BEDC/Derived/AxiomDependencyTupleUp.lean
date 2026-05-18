import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxiomDependencyTupleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxiomDependencyTupleCarrier [AskSetup] [PackageSetup]
    (mode witness supply transport route provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  (hsame mode BHist.Empty ∨
      hsame mode (BHist.e0 BHist.Empty) ∨ hsame mode (BHist.e1 BHist.Empty)) ∧
    UnaryHistory mode ∧ UnaryHistory witness ∧ UnaryHistory supply ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory localName ∧
        hsame transport transport ∧ Cont mode witness route ∧ Cont route supply localName ∧
          PkgSig bundle provenance pkg

theorem AxiomDependencyTupleCarrier_mode_exhaustion [AskSetup] [PackageSetup]
    {mode witness supply transport route provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxiomDependencyTupleCarrier mode witness supply transport route provenance localName
        bundle pkg →
      (hsame mode BHist.Empty ∨ hsame mode (BHist.e0 BHist.Empty) ∨
          hsame mode (BHist.e1 BHist.Empty)) ∧
        UnaryHistory witness ∧ UnaryHistory supply ∧ UnaryHistory route ∧
          UnaryHistory localName ∧ Cont mode witness route ∧
            Cont route supply localName ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory hsame Cont PkgSig
  intro carrier
  rcases carrier with
    ⟨modeCases, _modeUnary, witnessUnary, supplyUnary, _transportUnary, routeUnary,
      localNameUnary, _transportSame, modeWitnessRoute, routeSupplyLocalName,
      provenancePkg⟩
  exact
    ⟨modeCases, witnessUnary, supplyUnary, routeUnary, localNameUnary, modeWitnessRoute,
      routeSupplyLocalName, provenancePkg⟩

end BEDC.Derived.AxiomDependencyTupleUp
