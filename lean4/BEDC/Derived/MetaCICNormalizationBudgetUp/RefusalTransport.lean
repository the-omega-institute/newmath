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
    {R H Q L N refusalRead transportedRefusal replayedRefusal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory H →
        UnaryHistory Q →
          UnaryHistory L →
            UnaryHistory N →
              UnaryHistory refusalRead →
                Cont R Q refusalRead →
                  Cont H refusalRead transportedRefusal →
                    Cont transportedRefusal Q replayedRefusal →
                      PkgSig bundle L pkg →
                        PkgSig bundle replayedRefusal pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row replayedRefusal ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row R ∨ hsame row H ∨ hsame row Q ∨
                                  hsame row L ∨ hsame row N ∨ hsame row refusalRead ∨
                                    hsame row transportedRefusal ∨ hsame row replayedRefusal)
                              (fun row : BHist =>
                                hsame row replayedRefusal ∧ Cont R Q refusalRead ∧
                                  Cont H refusalRead transportedRefusal ∧
                                    Cont transportedRefusal Q replayedRefusal ∧
                                      PkgSig bundle replayedRefusal pkg)
                              hsame ∧
                            UnaryHistory transportedRefusal ∧
                              UnaryHistory replayedRefusal ∧ PkgSig bundle L pkg ∧
                                PkgSig bundle replayedRefusal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro _rUnary hUnary qUnary _lUnary _nUnary refusalUnary rq hRefusal transportReplay
    lPkg replayPkg
  have transportedUnary : UnaryHistory transportedRefusal :=
    unary_cont_closed hUnary refusalUnary hRefusal
  have replayedUnary : UnaryHistory replayedRefusal :=
    unary_cont_closed transportedUnary qUnary transportReplay
  have sourceReplay :
      (fun row : BHist => hsame row replayedRefusal ∧ UnaryHistory row)
        replayedRefusal := by
    exact ⟨hsame_refl replayedRefusal, replayedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayedRefusal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row H ∨ hsame row Q ∨ hsame row L ∨
              hsame row N ∨ hsame row refusalRead ∨ hsame row transportedRefusal ∨
                hsame row replayedRefusal)
          (fun row : BHist =>
            hsame row replayedRefusal ∧ Cont R Q refusalRead ∧
              Cont H refusalRead transportedRefusal ∧
                Cont transportedRefusal Q replayedRefusal ∧
                  PkgSig bundle replayedRefusal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayedRefusal sourceReplay
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, rq, hRefusal, transportReplay, replayPkg⟩
  }
  exact ⟨cert, transportedUnary, replayedUnary, lPkg, replayPkg⟩

end BEDC.Derived.MetaCICNormalizationBudgetUp
