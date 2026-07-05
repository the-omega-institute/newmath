import BEDC.Derived.ZetaContinuationSocketUp

namespace BEDC.Derived.ZetaContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationSocketCarrier_vision_concretization [AskSetup] [PackageSetup]
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
                  hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
                    hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                      hsame row transport ∨ hsame row route ∨ hsame row name ∨
                        hsame row sealRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont basic eta analytic ∧
                    Cont pole functional trivial ∧ Cont gamma transport route ∧
                      Cont analytic route analyticRead ∧
                        Cont analyticRead name sealRead ∧ PkgSig bundle route pkg ∧
                          PkgSig bundle name pkg ∧ PkgSig bundle sealRead pkg)
                hsame ∧
              UnaryHistory analyticRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: ZetaContinuationSocketCarrier BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier analyticReadRoute sealRoute sealPkg
  obtain ⟨_basicUnary, _etaUnary, analyticUnary, _poleUnary, _functionalUnary,
    _trivialUnary, _gammaUnary, _transportUnary, routeUnary, nameUnary, analyticRoute,
    trivialRoute, routeRoute, routePkg, namePkg⟩ := carrier
  have analyticReadUnary : UnaryHistory analyticRead :=
    unary_cont_closed analyticUnary routeUnary analyticReadRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed analyticReadUnary nameUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                hsame row transport ∨ hsame row route ∨ hsame row name ∨
                  hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont basic eta analytic ∧
              Cont pole functional trivial ∧ Cont gamma transport route ∧
                Cont analytic route analyticRead ∧ Cont analyticRead name sealRead ∧
                  PkgSig bundle route pkg ∧ PkgSig bundle name pkg ∧
                    PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact
        Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
          Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, analyticRoute, trivialRoute, routeRoute, analyticReadRoute,
          sealRoute, routePkg, namePkg, sealPkg⟩
  }
  exact ⟨cert, analyticReadUnary, sealUnary⟩

end BEDC.Derived.ZetaContinuationSocketUp
