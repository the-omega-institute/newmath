import BEDC.Derived.ArchimedeanOrderedFieldUp.Carrier

namespace BEDC.Derived.ArchimedeanOrderedFieldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ArchimedeanOrderedFieldComparisonLedgerExactness [AskSetup] [PackageSetup]
    {real alg rat bound ledger transport route provenance localCert comparisonRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ArchimedeanOrderedFieldCarrier real alg rat bound ledger transport route provenance
        localCert bundle pkg ->
      Cont ledger bound comparisonRead ->
        PkgSig bundle comparisonRead pkg ->
          UnaryHistory real ∧ UnaryHistory alg ∧ UnaryHistory rat ∧ UnaryHistory bound ∧
            UnaryHistory ledger ∧ UnaryHistory comparisonRead ∧ Cont real alg ledger ∧
              Cont ledger bound comparisonRead ∧ PkgSig bundle comparisonRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier comparisonRoute comparisonPkg
  obtain ⟨realUnary, algUnary, ratUnary, boundUnary, ledgerUnary, _provenanceUnary,
    _localCertUnary, realAlgLedger, _ledgerBoundRoute, _routeProvenanceCert,
      _provenancePkg, _localCertPkg⟩ := carrier
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed ledgerUnary boundUnary comparisonRoute
  exact
    ⟨realUnary, algUnary, ratUnary, boundUnary, ledgerUnary, comparisonUnary,
      realAlgLedger, comparisonRoute, comparisonPkg⟩

end BEDC.Derived.ArchimedeanOrderedFieldUp
