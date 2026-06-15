import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CoveringDimensionRootCoverOrderLedgerExhaustion [AskSetup] [PackageSetup]
    {K E C R O L H T P N coverRead refinementRead ledgerRead realRead completionRead
      orderRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionCarrier K E C R O L H T P N bundle pkg →
      Cont E C coverRead →
        Cont coverRead R refinementRead →
          Cont refinementRead L ledgerRead →
            Cont ledgerRead H realRead →
              Cont realRead T completionRead →
                Cont completionRead O orderRead →
                  Cont orderRead N namedRead →
                    PkgSig bundle namedRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨
                              hsame row L ∨ hsame row realRead ∨
                                hsame row completionRead ∨ hsame row O ∨
                                  hsame row namedRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont E C coverRead ∧
                              Cont coverRead R refinementRead ∧
                                Cont refinementRead L ledgerRead ∧
                                  Cont ledgerRead H realRead ∧
                                    Cont realRead T completionRead ∧
                                      Cont completionRead O orderRead ∧
                                        Cont orderRead N namedRead ∧
                                          PkgSig bundle namedRead pkg)
                          hsame ∧
                        UnaryHistory coverRead ∧ UnaryHistory refinementRead ∧
                          UnaryHistory ledgerRead ∧ UnaryHistory realRead ∧
                            UnaryHistory completionRead ∧ UnaryHistory orderRead ∧
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: CoveringDimensionCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier coverRoute refinementRoute ledgerRoute realRoute completionRoute orderRoute
    namedRoute namedPkg
  obtain ⟨_kUnary, eUnary, cUnary, rUnary, oUnary, lUnary, hUnary, tUnary, _pUnary,
    nUnary, _compactCover, _coverRefinement, _orderLedger, _realCompletion, _pPkg,
    _nPkg⟩ := carrier
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed eUnary cUnary coverRoute
  have refinementUnary : UnaryHistory refinementRead :=
    unary_cont_closed coverUnary rUnary refinementRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed refinementUnary lUnary ledgerRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed ledgerUnary hUnary realRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed realUnary tUnary completionRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed completionUnary oUnary orderRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed orderUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row E ∨ hsame row C ∨ hsame row R ∨ hsame row L ∨
              hsame row realRead ∨ hsame row completionRead ∨ hsame row O ∨
                hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont E C coverRead ∧ Cont coverRead R refinementRead ∧
              Cont refinementRead L ledgerRead ∧ Cont ledgerRead H realRead ∧
                Cont realRead T completionRead ∧ Cont completionRead O orderRead ∧
                  Cont orderRead N namedRead ∧ PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, coverRoute, refinementRoute, ledgerRoute, realRoute, completionRoute,
          orderRoute, namedRoute, namedPkg⟩
  }
  exact
    ⟨cert, coverUnary, refinementUnary, ledgerUnary, realUnary, completionUnary,
      orderUnary, namedUnary⟩

end BEDC.Derived.CoveringdimensionUp
