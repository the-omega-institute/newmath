import BEDC.Derived.MetaCICNormalizationBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICNormalizationBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICNormalizationBudgetCarrier_refusal_transport [AskSetup] [PackageSetup]
    {R H Q L refusalRead transportedRead replayedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory H →
        UnaryHistory Q →
          hsame H R →
            Cont R Q refusalRead →
              Cont H Q transportedRead →
                Cont transportedRead Q replayedRead →
                  PkgSig bundle L pkg →
                    PkgSig bundle replayedRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row replayedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row R ∨ hsame row H ∨ hsame row Q ∨
                              hsame row refusalRead ∨ hsame row transportedRead ∨
                                hsame row replayedRead)
                          (fun row : BHist =>
                            hsame row replayedRead ∧ Cont R Q refusalRead ∧
                              Cont H Q transportedRead ∧
                                Cont transportedRead Q replayedRead ∧
                                  PkgSig bundle replayedRead pkg)
                          hsame ∧
                        UnaryHistory refusalRead ∧ UnaryHistory transportedRead ∧
                          UnaryHistory replayedRead ∧ hsame transportedRead refusalRead ∧
                            Cont R Q refusalRead ∧ Cont H Q transportedRead ∧
                              Cont transportedRead Q replayedRead ∧
                                PkgSig bundle L pkg ∧ PkgSig bundle replayedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro rUnary hUnary qUnary sameHR refusalRoute transportedRoute replayedRoute lPkg
    replayedPkg
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed rUnary qUnary refusalRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed hUnary qUnary transportedRoute
  have replayedUnary : UnaryHistory replayedRead :=
    unary_cont_closed transportedUnary qUnary replayedRoute
  have sameTransportedRefusal : hsame transportedRead refusalRead :=
    cont_respects_hsame sameHR (hsame_refl Q) transportedRoute refusalRoute
  have sourceReplayed :
      (fun row : BHist => hsame row replayedRead ∧ UnaryHistory row) replayedRead :=
    ⟨hsame_refl replayedRead, replayedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row H ∨ hsame row Q ∨ hsame row refusalRead ∨
              hsame row transportedRead ∨ hsame row replayedRead)
          (fun row : BHist =>
            hsame row replayedRead ∧ Cont R Q refusalRead ∧
              Cont H Q transportedRead ∧ Cont transportedRead Q replayedRead ∧
                PkgSig bundle replayedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayedRead sourceReplayed
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute, transportedRoute, replayedRoute, replayedPkg⟩
  }
  exact
    ⟨cert, refusalUnary, transportedUnary, replayedUnary, sameTransportedRefusal,
      refusalRoute, transportedRoute, replayedRoute, lPkg, replayedPkg⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
