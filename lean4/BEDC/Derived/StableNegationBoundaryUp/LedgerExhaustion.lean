import BEDC.Derived.StableNegationBoundaryUp

namespace BEDC.Derived.StableNegationBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StableNegationBoundaryCarrier_ledger_exhaustion [AskSetup] [PackageSetup]
    {proposition refutation decision classifier ledger transport route provenance cert ledgerRead
      truthBlock : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    StableNegationBoundaryCarrier proposition refutation decision classifier ledger transport route
        provenance cert bundle pkg ->
      Cont ledger route ledgerRead ->
        Cont ledgerRead provenance truthBlock ->
          PkgSig bundle truthBlock pkg ->
            UnaryHistory ledgerRead ∧ UnaryHistory truthBlock ∧
              Cont proposition refutation classifier ∧ Cont decision classifier ledger ∧
                Cont ledger route ledgerRead ∧ Cont ledgerRead provenance truthBlock ∧
                  PkgSig bundle cert pkg ∧ PkgSig bundle truthBlock pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier ledgerRouteRead readProvenanceTruth truthPkg
  obtain ⟨_propositionUnary, _refutationUnary, _decisionUnary, _classifierUnary, ledgerUnary,
    _transportUnary, routeUnary, provenanceUnary, _certUnary, propositionRefutationClassifier,
    decisionClassifierLedger, _ledgerRouteProvenance, certSig⟩ := carrier
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed ledgerUnary routeUnary ledgerRouteRead
  have truthBlockUnary : UnaryHistory truthBlock :=
    unary_cont_closed ledgerReadUnary provenanceUnary readProvenanceTruth
  exact
    ⟨ledgerReadUnary, truthBlockUnary, propositionRefutationClassifier, decisionClassifierLedger,
      ledgerRouteRead, readProvenanceTruth, certSig, truthPkg⟩

end BEDC.Derived.StableNegationBoundaryUp
