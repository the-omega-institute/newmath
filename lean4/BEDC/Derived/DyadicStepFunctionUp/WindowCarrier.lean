import BEDC.Derived.DyadicStepFunctionUp

namespace BEDC.Derived.DyadicStepFunctionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicStepFunctionWindowCarrier [AskSetup] [PackageSetup]
    (cells refinement endpointLedger values reads ledger route provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  UnaryHistory cells ∧ UnaryHistory refinement ∧ UnaryHistory endpointLedger ∧
    UnaryHistory values ∧ UnaryHistory reads ∧ UnaryHistory ledger ∧ UnaryHistory route ∧
      UnaryHistory provenance ∧ UnaryHistory nameRow ∧ Cont cells refinement endpointLedger ∧
        Cont values reads ledger ∧ Cont ledger route nameRow ∧
          PkgSig bundle provenance pkg ∧ PkgSig bundle nameRow pkg

theorem DyadicStepFunctionWindowCarrier_public_read_closure [AskSetup] [PackageSetup]
    {cells refinement endpointLedger values reads ledger route provenance nameRow
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicStepFunctionWindowCarrier cells refinement endpointLedger values reads ledger route
        provenance nameRow bundle pkg ->
      Cont ledger route publicRead ->
        UnaryHistory publicRead ∧ UnaryHistory endpointLedger ∧ UnaryHistory ledger ∧
          Cont cells refinement endpointLedger ∧ Cont values reads ledger ∧
            Cont ledger route publicRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle nameRow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier publicRoute
  obtain ⟨_cellsUnary, _refinementUnary, endpointLedgerUnary, _valuesUnary, _readsUnary,
    ledgerUnary, routeUnary, _provenanceUnary, _nameRowUnary, cellsRefinementEndpoint,
    valuesReadsLedger, _ledgerRouteName, provenancePkg, nameRowPkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary routeUnary publicRoute
  exact
    ⟨publicReadUnary, endpointLedgerUnary, ledgerUnary, cellsRefinementEndpoint,
      valuesReadsLedger, publicRoute, provenancePkg, nameRowPkg⟩

end BEDC.Derived.DyadicStepFunctionUp
