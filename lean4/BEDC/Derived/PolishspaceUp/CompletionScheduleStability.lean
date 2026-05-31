import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompletionScheduleStability [AskSetup] [PackageSetup]
    {metric complete stream readback ledger transport replay scheduledRead completionSchedule
      provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric ->
      UnaryHistory complete ->
        UnaryHistory stream ->
          UnaryHistory readback ->
            UnaryHistory ledger ->
              UnaryHistory transport ->
                Cont metric complete scheduledRead ->
                  Cont scheduledRead stream completionSchedule ->
                    Cont ledger transport replay ->
                      PkgSig bundle provenance pkg ->
                        PkgSig bundle localName pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row completionSchedule ∧
                                UnaryHistory row)
                              (fun row : BHist =>
                                hsame row metric ∨ hsame row complete ∨ hsame row stream ∨
                                  hsame row readback ∨ hsame row ledger ∨
                                    hsame row completionSchedule)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory scheduledRead ∧ UnaryHistory completionSchedule ∧
                              UnaryHistory replay := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro metricUnary completeUnary streamUnary _readbackUnary ledgerUnary transportUnary
    metricCompleteScheduled scheduledStreamCompletion ledgerTransportReplay provenancePkg
    localNamePkg
  have scheduledUnary : UnaryHistory scheduledRead :=
    unary_cont_closed metricUnary completeUnary metricCompleteScheduled
  have completionUnary : UnaryHistory completionSchedule :=
    unary_cont_closed scheduledUnary streamUnary scheduledStreamCompletion
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportReplay
  have sourceCompletion :
      (fun row : BHist => hsame row completionSchedule ∧ UnaryHistory row)
        completionSchedule := by
    exact ⟨hsame_refl completionSchedule, completionUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionSchedule ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row complete ∨ hsame row stream ∨
              hsame row readback ∨ hsame row ledger ∨ hsame row completionSchedule)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro completionSchedule sourceCompletion
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
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, scheduledUnary, completionUnary, replayUnary⟩

end BEDC.Derived.PolishspaceUp
