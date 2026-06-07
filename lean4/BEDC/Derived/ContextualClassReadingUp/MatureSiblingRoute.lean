import BEDC.Derived.ContextualClassReadingUp

namespace BEDC.Derived.ContextualClassReadingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContextualClassReadingCarrier_mature_sibling_route [AskSetup] [PackageSetup]
    {expression context relation scope transport route provenance localName russellBoundary
      russellLadder matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory russellBoundary ->
      UnaryHistory russellLadder ->
        ContextualClassReadingCarrier expression context relation scope transport route provenance
          localName bundle pkg ->
          Cont russellBoundary russellLadder expression ->
            Cont relation scope matureRead ->
              PkgSig bundle matureRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row russellBoundary ∨ hsame row russellLadder ∨
                        hsame row expression ∨ hsame row context ∨ hsame row relation ∨
                          hsame row scope ∨ hsame row matureRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont russellBoundary russellLadder expression ∧
                        Cont expression context relation ∧ Cont relation scope matureRead ∧
                          PkgSig bundle matureRead pkg)
                    hsame ∧
                  UnaryHistory matureRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro russellBoundaryUnary russellLadderUnary carrier russellExpressionRoute
    matureRoute maturePkg
  obtain ⟨expressionUnary, _contextUnary, relationUnary, scopeUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _localNameUnary, expressionContextRelation,
    _relationScopeRoute, _routeTransportProvenance, _localNamePkg⟩ := carrier
  have _expressionUnaryFromSiblings : UnaryHistory expression :=
    unary_cont_closed russellBoundaryUnary russellLadderUnary russellExpressionRoute
  have matureUnary : UnaryHistory matureRead :=
    unary_cont_closed relationUnary scopeUnary matureRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row russellBoundary ∨ hsame row russellLadder ∨ hsame row expression ∨
              hsame row context ∨ hsame row relation ∨ hsame row scope ∨
                hsame row matureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont russellBoundary russellLadder expression ∧
              Cont expression context relation ∧ Cont relation scope matureRead ∧
                PkgSig bundle matureRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro matureRead ⟨hsame_refl matureRead, matureUnary⟩
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
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, russellExpressionRoute, expressionContextRelation, matureRoute,
          maturePkg⟩
  }
  exact ⟨cert, matureUnary⟩

end BEDC.Derived.ContextualClassReadingUp
