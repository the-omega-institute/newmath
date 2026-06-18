import BEDC.Derived.AuditMapObstructionSocketUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuditMapObstructionSocketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditMapObstructionSocketNameCertObligations [AskSetup] [PackageSetup]
    {A P I O F H C K N positiveRead conditionalRead obstructionRead frontierRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A ->
      UnaryHistory P ->
        UnaryHistory I ->
          UnaryHistory O ->
            UnaryHistory F ->
              UnaryHistory H ->
                UnaryHistory K ->
                  Cont A P positiveRead ->
                    Cont positiveRead I conditionalRead ->
                      Cont conditionalRead O obstructionRead ->
                        Cont obstructionRead F frontierRead ->
                          Cont frontierRead H C ->
                            Cont C K N ->
                              PkgSig bundle K pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row A ∨ hsame row P ∨ hsame row I ∨
                                          hsame row O ∨ hsame row F ∨
                                            hsame row frontierRead ∨ hsame row N)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ PkgSig bundle K pkg ∧
                                          PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory positiveRead ∧
                                      UnaryHistory conditionalRead ∧
                                        UnaryHistory obstructionRead ∧
                                          UnaryHistory frontierRead ∧ UnaryHistory C ∧
                                            UnaryHistory N := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro aUnary pUnary iUnary oUnary fUnary hUnary kUnary positiveRoute conditionalRoute
    obstructionRoute frontierRoute frontierReplay nameRoute provenancePkg namePkg
  have positiveUnary : UnaryHistory positiveRead :=
    unary_cont_closed aUnary pUnary positiveRoute
  have conditionalUnary : UnaryHistory conditionalRead :=
    unary_cont_closed positiveUnary iUnary conditionalRoute
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed conditionalUnary oUnary obstructionRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed obstructionUnary fUnary frontierRoute
  have cUnary : UnaryHistory C :=
    unary_cont_closed frontierUnary hUnary frontierReplay
  have nUnary : UnaryHistory N :=
    unary_cont_closed cUnary kUnary nameRoute
  have sourceName :
      (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, nUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row P ∨ hsame row I ∨ hsame row O ∨
              hsame row F ∨ hsame row frontierRead ∨ hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle K pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceName
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
        exact ⟨source.right, provenancePkg, namePkg⟩
    }
  exact
    ⟨cert, positiveUnary, conditionalUnary, obstructionUnary, frontierUnary, cUnary, nUnary⟩

end BEDC.Derived.AuditMapObstructionSocketUp
