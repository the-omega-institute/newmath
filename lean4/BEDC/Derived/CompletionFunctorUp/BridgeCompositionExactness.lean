import BEDC.Derived.CompletionFunctorUp

namespace BEDC.Derived.CompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompletionFunctorCarrier_bridge_composition_exactness [AskSetup] [PackageSetup]
    {monad universal realCompletion source target denseMap extension functorLedger transport
      routes provenance name firstSeal secondSeal bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompletionFunctorCarrier monad universal realCompletion source target denseMap extension
        functorLedger transport routes provenance name bundle pkg →
      Cont target firstSeal secondSeal →
        hsame secondSeal source →
          Cont secondSeal extension bridgeRead →
            PkgSig bundle bridgeRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row target ∨ hsame row firstSeal ∨ hsame row secondSeal ∨
                      hsame row bridgeRead ∨ hsame row extension ∨ hsame row provenance)
                  (fun row : BHist =>
                    UnaryHistory row ∧ hsame secondSeal source ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle bridgeRead pkg)
                  hsame ∧
                UnaryHistory firstSeal ∧ UnaryHistory secondSeal ∧
                  UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier firstSealRoute sameSecondSource bridgeRoute bridgePkg
  obtain ⟨_monadUnary, _universalUnary, _realCompletionUnary, sourceUnary, _targetUnary,
    _denseMapUnary, extensionUnary, _functorLedgerUnary, _transportUnary, _routesUnary,
    _provenanceUnary, _nameUnary, _monadRoute, _denseMapRoute, _extensionRoute,
    _functorRoute, _transportRoute, provenancePkg, _namePkg⟩ := carrier
  have secondSealUnary : UnaryHistory secondSeal :=
    unary_transport_symm sourceUnary sameSecondSource
  have firstSealUnary : UnaryHistory firstSeal :=
    unary_cont_right_factor firstSealRoute secondSealUnary
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed secondSealUnary extensionUnary bridgeRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row target ∨ hsame row firstSeal ∨ hsame row secondSeal ∨
            hsame row bridgeRead ∨ hsame row extension ∨ hsame row provenance)
        (fun row : BHist =>
          UnaryHistory row ∧ hsame secondSeal source ∧ PkgSig bundle provenance pkg ∧
            PkgSig bundle bridgeRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead (And.intro (hsame_refl bridgeRead) bridgeUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        have sameBridge : hsame _ bridgeRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have rowUnary : UnaryHistory _ :=
          unary_transport source.right sameRows
        exact And.intro sameBridge rowUnary
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact
        And.intro source.right
          (And.intro sameSecondSource (And.intro provenancePkg bridgePkg))
  }
  exact ⟨cert, firstSealUnary, secondSealUnary, bridgeUnary⟩

end BEDC.Derived.CompletionFunctorUp
