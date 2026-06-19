import BEDC.Derived.MetaCICNormalizationBudgetUp.RefusalTransport

namespace BEDC.Derived.MetaCICNormalizationBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationBudgetCarrier_refusal_idempotence [AskSetup] [PackageSetup]
    {R H Q L refusalRead transportedRead replayedRead replayedAgain : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory H →
        UnaryHistory Q →
          hsame H R →
            Cont R Q refusalRead →
              Cont H Q transportedRead →
                Cont transportedRead Q replayedRead →
                  Cont replayedRead Q replayedAgain →
                    PkgSig bundle L pkg →
                      PkgSig bundle replayedAgain pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row replayedAgain ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row R ∨ hsame row H ∨ hsame row Q ∨
                                hsame row refusalRead ∨ hsame row transportedRead ∨
                                  hsame row replayedRead ∨ hsame row replayedAgain)
                            (fun row : BHist =>
                              hsame row replayedAgain ∧ Cont R Q refusalRead ∧
                                Cont H Q transportedRead ∧
                                  Cont transportedRead Q replayedRead ∧
                                    Cont replayedRead Q replayedAgain ∧
                                      PkgSig bundle replayedAgain pkg)
                            hsame ∧
                          UnaryHistory refusalRead ∧ UnaryHistory transportedRead ∧
                            UnaryHistory replayedRead ∧ UnaryHistory replayedAgain ∧
                              hsame transportedRead refusalRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro rUnary hUnary qUnary sameHR refusalRoute transportedRoute replayedRoute
    replayedAgainRoute _lPkg replayedAgainPkg
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed rUnary qUnary refusalRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed hUnary qUnary transportedRoute
  have replayedUnary : UnaryHistory replayedRead :=
    unary_cont_closed transportedUnary qUnary replayedRoute
  have replayedAgainUnary : UnaryHistory replayedAgain :=
    unary_cont_closed replayedUnary qUnary replayedAgainRoute
  have sameTransportedRefusal : hsame transportedRead refusalRead :=
    cont_respects_hsame sameHR (hsame_refl Q) transportedRoute refusalRoute
  have sourceReplayedAgain :
      (fun row : BHist => hsame row replayedAgain ∧ UnaryHistory row) replayedAgain :=
    ⟨hsame_refl replayedAgain, replayedAgainUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayedAgain ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row H ∨ hsame row Q ∨ hsame row refusalRead ∨
              hsame row transportedRead ∨ hsame row replayedRead ∨ hsame row replayedAgain)
          (fun row : BHist =>
            hsame row replayedAgain ∧ Cont R Q refusalRead ∧
              Cont H Q transportedRead ∧ Cont transportedRead Q replayedRead ∧
                Cont replayedRead Q replayedAgain ∧ PkgSig bundle replayedAgain pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayedAgain sourceReplayedAgain
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
      exact
        ⟨source.left, refusalRoute, transportedRoute, replayedRoute,
          replayedAgainRoute, replayedAgainPkg⟩
  }
  exact
    ⟨cert, refusalUnary, transportedUnary, replayedUnary, replayedAgainUnary,
      sameTransportedRefusal⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
