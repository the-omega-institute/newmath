import BEDC.Derived.ZetaContinuationSocketUp

namespace BEDC.Derived.ZetaContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationSocketCarrier_analytic_handoff [AskSetup] [PackageSetup]
    {basic eta analytic pole functional trivial gamma transport route name analyticRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationSocketCarrier basic eta analytic pole functional trivial gamma transport
        route name bundle pkg →
      Cont analytic route analyticRead →
        Cont analyticRead name sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row route ∨
                    hsame row name ∨ hsame row analyticRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont analytic route analyticRead ∧
                    Cont analyticRead name sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory analyticRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier analyticRoute sealRoute sealPkg
  obtain ⟨_basicUnary, _etaUnary, analyticUnary, _poleUnary, _functionalUnary,
    _trivialUnary, _gammaUnary, _transportUnary, routeUnary, nameUnary, _carrierAnalyticRoute,
    _carrierTrivialRoute, _carrierRouteRoute, _routePkg, _namePkg⟩ := carrier
  have analyticReadUnary : UnaryHistory analyticRead :=
    unary_cont_closed analyticUnary routeUnary analyticRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed analyticReadUnary nameUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row route ∨
              hsame row name ∨ hsame row analyticRead ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont analytic route analyticRead ∧
              Cont analyticRead name sealRead ∧ PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨sealRead, hsame_refl sealRead, sealReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, analyticRoute, sealRoute, sealPkg⟩
  }
  exact ⟨cert, analyticReadUnary, sealReadUnary⟩

theorem ZetaContinuationSocketCarrier_analytic_ledger_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional trivial gamma transport route name analyticRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationSocketCarrier basic eta analytic pole functional trivial gamma transport
        route name bundle pkg →
      Cont analytic route analyticRead →
        Cont analyticRead name sealRead →
          PkgSig bundle sealRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row route ∨
                    hsame row name ∨ hsame row analyticRead ∨ hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont analytic route analyticRead ∧
                    Cont analyticRead name sealRead ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              SemanticNameCert
                  (fun row : BHist => hsame row pole ∨ hsame row gamma ∨ hsame row trivial)
                  (fun row : BHist =>
                    hsame row pole ∨ hsame row gamma ∨ hsame row trivial ∨
                      hsame row analytic ∨ hsame row route)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle route pkg ∧ PkgSig bundle name pkg)
                  hsame ∧
                UnaryHistory analyticRead ∧ UnaryHistory sealRead ∧
                  UnaryHistory pole ∧ UnaryHistory gamma ∧ UnaryHistory trivial := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier analyticRoute sealRoute sealPkg
  obtain ⟨handoffCert, analyticReadUnary, sealReadUnary⟩ :=
    ZetaContinuationSocketCarrier_analytic_handoff
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (trivial := trivial) (gamma := gamma)
      (transport := transport) (route := route) (name := name)
      (analyticRead := analyticRead) (sealRead := sealRead) (bundle := bundle) (pkg := pkg)
      carrier analyticRoute sealRoute sealPkg
  obtain ⟨ledgerCert, poleUnary, gammaUnary, trivialUnary⟩ :=
    ZetaContinuationSocketLedger_nonescape
      (basic := basic) (eta := eta) (analytic := analytic) (pole := pole)
      (functional := functional) (trivial := trivial) (gamma := gamma)
      (transport := transport) (route := route) (name := name)
      (bundle := bundle) (pkg := pkg) carrier
  exact
    ⟨handoffCert, ledgerCert, analyticReadUnary, sealReadUnary, poleUnary, gammaUnary,
      trivialUnary⟩

end BEDC.Derived.ZetaContinuationSocketUp
