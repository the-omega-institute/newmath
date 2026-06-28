import BEDC.Derived.RealCompletionSelectorSealUp

namespace BEDC.Derived.RealCompletionSelectorSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionSelectorSealCarrier_selector_budget_totality [AskSetup]
    [PackageSetup]
    {b w r l e h c p n selectorRead endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletionSelectorSealCarrier b w r l e h c p n bundle pkg ->
      Cont b w selectorRead ->
        Cont selectorRead r endpointRead ->
          PkgSig bundle endpointRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row b ∨ hsame row w ∨ hsame row r ∨ hsame row selectorRead ∨
                    hsame row endpointRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont b w selectorRead ∧
                    Cont selectorRead r endpointRead ∧ PkgSig bundle endpointRead pkg)
                hsame ∧ UnaryHistory selectorRead ∧ UnaryHistory endpointRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier selectorRoute endpointRoute endpointPkg
  obtain ⟨bUnary, wUnary, rUnary, _lUnary, _eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _budgetWindowReadback, _readbackLimitEndpoint, _provenancePkg,
    _hName⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed bUnary wUnary selectorRoute
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed selectorUnary rUnary endpointRoute
  refine ⟨?_, selectorUnary, endpointUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨endpointRead, hsame_refl endpointRead, endpointUnary⟩
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · intro row _source
    exact hsame_refl row
  · intro _row _row' sameRows
    exact hsame_symm sameRows
  · intro _row _row' _row'' sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _row' sameRows sourceRow
    exact
      ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
        unary_transport sourceRow.right sameRows⟩
  · intro _row sourceRow
    exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
  · intro _row sourceRow
    exact ⟨sourceRow.right, selectorRoute, endpointRoute, endpointPkg⟩

end BEDC.Derived.RealCompletionSelectorSealUp
