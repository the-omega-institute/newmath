import BEDC.Derived.DiagonallimitcompatibilityUp.RootFormalSource

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootFormalSealFactorization [AskSetup] [PackageSetup]
    {budget selector window regseq realSeal transport route provenance cert sealRead final :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityRootFormalSource budget selector window regseq realSeal transport
        route provenance cert bundle pkg ->
      Cont realSeal cert sealRead ->
        Cont sealRead route final ->
          PkgSig bundle final pkg ->
            UnaryHistory budget ∧ UnaryHistory selector ∧ UnaryHistory window ∧
              UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory sealRead ∧
                UnaryHistory final ∧ Cont budget selector window ∧
                  Cont window regseq realSeal ∧ Cont realSeal cert sealRead ∧
                    Cont sealRead route final ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle final pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro source realSealCertSealRead sealReadRouteFinal finalPkg
  rcases source with
    ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary,
      _transportUnary, routeUnary, _provenanceUnary, certUnary, budgetSelectorWindow,
      windowRegseqRealSeal, _transportRouteCert, provenancePkg⟩
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed realSealUnary certUnary realSealCertSealRead
  have finalUnary : UnaryHistory final :=
    unary_cont_closed sealReadUnary routeUnary sealReadRouteFinal
  exact
    ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary, sealReadUnary,
      finalUnary, budgetSelectorWindow, windowRegseqRealSeal, realSealCertSealRead,
      sealReadRouteFinal, provenancePkg, finalPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
