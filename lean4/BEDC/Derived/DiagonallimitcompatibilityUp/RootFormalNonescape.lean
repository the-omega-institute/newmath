import BEDC.Derived.DiagonallimitcompatibilityUp.RootFormalSource

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootFormalNonescape [AskSetup] [PackageSetup]
    {budget selector window regseq realSeal transport route provenance cert externalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityRootFormalSource budget selector window regseq realSeal transport
        route provenance cert bundle pkg ->
      Cont realSeal cert externalRead ->
        PkgSig bundle externalRead pkg ->
          UnaryHistory budget ∧ UnaryHistory selector ∧ UnaryHistory window ∧
            UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory cert ∧
              UnaryHistory externalRead ∧ Cont budget selector window ∧
                Cont window regseq realSeal ∧ Cont realSeal cert externalRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle externalRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle
  intro source realSealCertExternalRead externalReadPkg
  obtain ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary,
    _transportUnary, _routeUnary, _provenanceUnary, certUnary, budgetSelectorWindow,
    windowRegseqRealSeal, _transportRouteCert, provenancePkg⟩ := source
  have externalReadUnary : UnaryHistory externalRead :=
    unary_cont_closed realSealUnary certUnary realSealCertExternalRead
  exact
    ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary, certUnary,
      externalReadUnary, budgetSelectorWindow, windowRegseqRealSeal,
      realSealCertExternalRead, provenancePkg, externalReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
