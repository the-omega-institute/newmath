import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.StableNegationBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def StableNegationBoundaryCarrier [AskSetup] [PackageSetup]
    (proposition refutation decision classifier ledger transport route provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory proposition ∧ UnaryHistory refutation ∧ UnaryHistory decision ∧
    UnaryHistory classifier ∧ UnaryHistory ledger ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont proposition refutation classifier ∧ Cont decision classifier ledger ∧
          Cont ledger route provenance ∧ PkgSig bundle cert pkg

theorem StableNegationBoundaryCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {proposition refutation decision classifier ledger transport route provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StableNegationBoundaryCarrier proposition refutation decision classifier ledger transport route
        provenance cert bundle pkg ->
      UnaryHistory proposition ∧ UnaryHistory refutation ∧ UnaryHistory decision ∧
        UnaryHistory classifier ∧ UnaryHistory ledger ∧ Cont proposition refutation classifier ∧
          Cont decision classifier ledger ∧ Cont ledger route provenance ∧
            PkgSig bundle cert pkg := by
  intro packet
  obtain ⟨propositionUnary, refutationUnary, decisionUnary, classifierUnary, ledgerUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _certUnary, refutationClassifier,
    decisionLedger, ledgerProvenance, certSig⟩ := packet
  exact
    ⟨propositionUnary, refutationUnary, decisionUnary, classifierUnary, ledgerUnary,
      refutationClassifier, decisionLedger, ledgerProvenance, certSig⟩

end BEDC.Derived.StableNegationBoundaryUp
