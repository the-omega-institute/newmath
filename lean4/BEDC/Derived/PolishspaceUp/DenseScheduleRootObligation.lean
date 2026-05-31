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

theorem PolishSpaceDenseScheduleRootObligation [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      denseRead scheduleRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory separable →
        UnaryHistory stream →
          UnaryHistory readback →
            UnaryHistory ledger →
              UnaryHistory transport →
                Cont separable stream denseRead →
                  Cont ledger transport replay →
                    Cont replay readback scheduleRead →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          SemanticNameCert
                              (fun row : BHist => hsame row scheduleRead ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row metric ∨ hsame row separable ∨ hsame row stream ∨
                                  hsame row readback ∨ hsame row ledger ∨ hsame row scheduleRead)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                                  PkgSig bundle localName pkg)
                              hsame ∧
                            UnaryHistory denseRead ∧ UnaryHistory scheduleRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro _metricUnary separableUnary streamUnary readbackUnary ledgerUnary transportUnary
    separableStreamDense ledgerTransportReplay replayReadbackSchedule provenancePkg localNamePkg
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary separableStreamDense
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerTransportReplay
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed replayUnary readbackUnary replayReadbackSchedule
  have sourceSchedule :
      (fun row : BHist => hsame row scheduleRead ∧ UnaryHistory row) scheduleRead := by
    exact ⟨hsame_refl scheduleRead, scheduleUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scheduleRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row separable ∨ hsame row stream ∨
              hsame row readback ∨ hsame row ledger ∨ hsame row scheduleRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scheduleRead sourceSchedule
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
  exact ⟨cert, denseUnary, scheduleUnary⟩

end BEDC.Derived.PolishspaceUp
