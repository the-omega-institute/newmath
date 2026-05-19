import BEDC.Derived.DiagonallimitcompatibilityUp.RootFormalSource

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DiagonalLimitCompatibilityRootFormalAuditSurface [AskSetup] [PackageSetup]
    {budget selector window regseq realSeal transport route provenance name auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityRootFormalSource budget selector window regseq realSeal transport
        route provenance name bundle pkg →
      Cont realSeal route auditRead →
        PkgSig bundle auditRead pkg →
          UnaryHistory budget ∧ UnaryHistory selector ∧ UnaryHistory window ∧
            UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory route ∧
              UnaryHistory auditRead ∧ Cont budget selector window ∧
                Cont window regseq realSeal ∧ Cont realSeal route auditRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro source realSealRouteAuditRead auditReadPkg
  obtain ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary,
    _transportUnary, routeUnary, _provenanceUnary, _nameUnary, budgetSelectorWindow,
    windowRegseqRealSeal, _transportRouteName, provenancePkg⟩ := source
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed realSealUnary routeUnary realSealRouteAuditRead
  exact
    ⟨budgetUnary, selectorUnary, windowUnary, regseqUnary, realSealUnary, routeUnary,
      auditReadUnary, budgetSelectorWindow, windowRegseqRealSeal, realSealRouteAuditRead,
      provenancePkg, auditReadPkg⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
