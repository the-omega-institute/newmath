import BEDC.Derived.MetaCICCriticalPathUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathRealStreamNameSourceReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal sourceSchedule : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg ->
      Cont stream realSeal sourceSchedule ->
        PkgSig bundle sourceSchedule pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row sourceSchedule ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row sourceSchedule)
              (fun row : BHist =>
                hsame row sourceSchedule ∧ PkgSig bundle sourceSchedule pkg ∧
                  PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory sourceSchedule ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger streamRealSealSource sourceSchedulePkg
  obtain ⟨_packet, _dyadicUnary, streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have sourceScheduleUnary : UnaryHistory sourceSchedule :=
    unary_cont_closed streamUnary realSealUnary streamRealSealSource
  have sourceScheduleCarrier :
      (fun row : BHist => hsame row sourceSchedule ∧ UnaryHistory row)
        sourceSchedule := by
    exact ⟨hsame_refl sourceSchedule, sourceScheduleUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceSchedule ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row sourceSchedule)
          (fun row : BHist =>
            hsame row sourceSchedule ∧ PkgSig bundle sourceSchedule pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceSchedule sourceScheduleCarrier
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sourceSchedulePkg, realSealPkg⟩
  }
  exact ⟨cert, sourceScheduleUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
