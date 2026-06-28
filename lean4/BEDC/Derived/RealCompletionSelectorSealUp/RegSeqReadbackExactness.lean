import BEDC.Derived.RealCompletionSelectorSealUp

namespace BEDC.Derived.RealCompletionSelectorSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionSelectorSealCarrier_regseq_readback_exactness [AskSetup]
    [PackageSetup]
    {b w r l e h c p n windowRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealCompletionSelectorSealCarrier b w r l e h c p n bundle pkg ->
      Cont b w windowRead ->
        Cont windowRead r readbackRead ->
          Cont readbackRead l sealRead ->
            PkgSig bundle sealRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row b ∨ hsame row w ∨ hsame row r ∨ hsame row l ∨
                      hsame row windowRead ∨ hsame row readbackRead ∨
                        hsame row sealRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont b w windowRead ∧
                      Cont windowRead r readbackRead ∧ Cont readbackRead l sealRead ∧
                        PkgSig bundle sealRead pkg)
                  hsame ∧ UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier windowRoute readbackRoute sealRoute sealPkg
  obtain ⟨bUnary, wUnary, rUnary, lUnary, _eUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _budgetWindowReadback, _readbackLimitEndpoint, _provenancePkg,
    _hName⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary lUnary sealRoute
  refine ⟨?_, windowUnary, readbackUnary, sealUnary⟩
  refine
    { core :=
        { carrier_inhabited := ⟨sealRead, hsame_refl sealRead, sealUnary⟩
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
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
  · intro _row sourceRow
    exact ⟨sourceRow.right, windowRoute, readbackRoute, sealRoute, sealPkg⟩

end BEDC.Derived.RealCompletionSelectorSealUp
