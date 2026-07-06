import BEDC.Derived.ZetaContinuationSocketUp

namespace BEDC.Derived.ZetaContinuationSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationSocketCarrier_functional_equation_boundary [AskSetup] [PackageSetup]
    {basic eta analytic pole functional trivial gamma transport route name functionalRead
      witnessRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationSocketCarrier basic eta analytic pole functional trivial gamma transport
        route name bundle pkg →
      Cont functional gamma functionalRead →
        Cont functionalRead route witnessRead →
          PkgSig bundle witnessRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨
                    hsame row pole ∨ hsame row functional ∨ hsame row trivial ∨
                      hsame row gamma ∨ hsame row transport ∨ hsame row route ∨
                        hsame row name ∨ hsame row functionalRead ∨
                          hsame row witnessRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont functional gamma functionalRead ∧
                    Cont functionalRead route witnessRead ∧ PkgSig bundle witnessRead pkg)
                hsame ∧
              UnaryHistory functionalRead ∧ UnaryHistory witnessRead ∧
                UnaryHistory functional := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier functionalRoute witnessRoute witnessPkg
  obtain ⟨_basicUnary, _etaUnary, _analyticUnary, _poleUnary, functionalUnary,
    _trivialUnary, gammaUnary, _transportUnary, routeUnary, _nameUnary, _analyticRoute,
    _trivialRoute, _routeRoute, _routePkg, _namePkg⟩ := carrier
  have functionalReadUnary : UnaryHistory functionalRead :=
    unary_cont_closed functionalUnary gammaUnary functionalRoute
  have witnessReadUnary : UnaryHistory witnessRead :=
    unary_cont_closed functionalReadUnary routeUnary witnessRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row basic ∨ hsame row eta ∨ hsame row analytic ∨ hsame row pole ∨
              hsame row functional ∨ hsame row trivial ∨ hsame row gamma ∨
                hsame row transport ∨ hsame row route ∨ hsame row name ∨
                  hsame row functionalRead ∨ hsame row witnessRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont functional gamma functionalRead ∧
              Cont functionalRead route witnessRead ∧ PkgSig bundle witnessRead pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨witnessRead, hsame_refl witnessRead, witnessReadUnary⟩
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
          Or.inr <| Or.inr <| Or.inr <| Or.inr <| source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, functionalRoute, witnessRoute, witnessPkg⟩
  }
  exact ⟨cert, functionalReadUnary, witnessReadUnary, functionalUnary⟩

end BEDC.Derived.ZetaContinuationSocketUp
