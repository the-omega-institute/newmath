import BEDC.Derived.DiagonallimitcompatibilityUp.RootFormalSource

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootReadbackDeterminacy [AskSetup] [PackageSetup]
    {budget selector window regseq realSeal transport route provenance cert localReadback
      finalReadback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityRootFormalSource budget selector window regseq realSeal transport
        route provenance cert bundle pkg ->
      Cont transport route localReadback ->
        Cont localReadback cert finalReadback ->
          PkgSig bundle finalReadback pkg ->
            UnaryHistory budget ∧ UnaryHistory selector ∧ UnaryHistory window ∧
              UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory transport ∧
                UnaryHistory route ∧ UnaryHistory cert ∧ UnaryHistory localReadback ∧
                  UnaryHistory finalReadback ∧ Cont budget selector window ∧
                    Cont window regseq realSeal ∧ Cont transport route localReadback ∧
                      Cont localReadback cert finalReadback ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle finalReadback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro source transportRouteLocalReadback localCertFinalReadback finalReadbackPkg
  rcases source with
    ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary,
      transportUnary, routeUnary, _provenanceUnary, certUnary, budgetSelectorWindow,
      windowRegseqRealSeal, _transportRouteCert, provenancePkg⟩
  have localReadbackUnary : UnaryHistory localReadback :=
    unary_cont_closed transportUnary routeUnary transportRouteLocalReadback
  have finalReadbackUnary : UnaryHistory finalReadback :=
    unary_cont_closed localReadbackUnary certUnary localCertFinalReadback
  exact
    ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary, transportUnary,
      routeUnary, certUnary, localReadbackUnary, finalReadbackUnary, budgetSelectorWindow,
      windowRegseqRealSeal, transportRouteLocalReadback, localCertFinalReadback,
      provenancePkg, finalReadbackPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
