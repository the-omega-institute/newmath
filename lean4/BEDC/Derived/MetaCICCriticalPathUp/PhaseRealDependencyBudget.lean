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

theorem MetaCICCriticalPathL10SourceCut [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal sourceCut : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream sourceCut →
        PkgSig bundle sourceCut pkg →
          SemanticNameCert
              (fun row : BHist => hsame row sourceCut ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row sourceCut)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle sourceCut pkg ∧
                  Cont dyadic stream sourceCut)
              hsame ∧
            UnaryHistory sourceCut ∧ Cont dyadic stream regseq := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger dyadicStreamSourceCut sourceCutPkg
  obtain ⟨_packet, dyadicUnary, streamUnary, _regseqUnary, _realSealUnary,
    dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  have sourceCutUnary : UnaryHistory sourceCut :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamSourceCut
  have sourceCutCarrier :
      (fun row : BHist => hsame row sourceCut ∧ UnaryHistory row) sourceCut := by
    exact ⟨hsame_refl sourceCut, sourceCutUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceCut ∧ UnaryHistory row)
          (fun row : BHist => hsame row dyadic ∨ hsame row stream ∨ hsame row sourceCut)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle sourceCut pkg ∧
              Cont dyadic stream sourceCut)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceCut sourceCutCarrier
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceCutPkg, dyadicStreamSourceCut⟩
  }
  exact ⟨cert, sourceCutUnary, dyadicStreamRegseq⟩

theorem MetaCICCriticalPathStreamNameRegSeqRatRouteOrder [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName streamSchedule regSeqReadback realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName streamSchedule →
        Cont streamSchedule localName regSeqReadback →
          Cont regSeqReadback localName realSeal →
            PkgSig bundle streamSchedule pkg →
              PkgSig bundle regSeqReadback pkg →
                PkgSig bundle realSeal pkg →
                  UnaryHistory streamSchedule ∧ UnaryHistory regSeqReadback ∧
                    UnaryHistory realSeal ∧ Cont route localName streamSchedule ∧
                      Cont streamSchedule localName regSeqReadback ∧
                        Cont regSeqReadback localName realSeal ∧
                          PkgSig bundle provenance pkg ∧
                            PkgSig bundle streamSchedule pkg ∧
                              PkgSig bundle regSeqReadback pkg ∧
                                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle UnaryHistory
  intro packet routeLocalNameSchedule scheduleLocalNameReadback readbackLocalNameSeal
    streamSchedulePkg regSeqReadbackPkg realSealPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSchedule
  have regSeqReadbackUnary : UnaryHistory regSeqReadback :=
    unary_cont_closed streamScheduleUnary localNameUnary scheduleLocalNameReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regSeqReadbackUnary localNameUnary readbackLocalNameSeal
  exact
    ⟨streamScheduleUnary, regSeqReadbackUnary, realSealUnary, routeLocalNameSchedule,
      scheduleLocalNameReadback, readbackLocalNameSeal, provenancePkg, streamSchedulePkg,
      regSeqReadbackPkg, realSealPkg⟩

theorem MetaCICCriticalPathPhaseRealExitConjunction [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal exitRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal exitRead →
          PkgSig bundle exitRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row exitRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row exitRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont dyadic stream regseq ∧
                    Cont regseq realSeal exitRead ∧ PkgSig bundle exitRead pkg)
                hsame ∧
              UnaryHistory exitRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger dyadicStreamRegseq regseqRealSealExit exitReadPkg
  obtain ⟨_packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have exitReadUnary : UnaryHistory exitRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealExit
  have exitReadCarrier :
      (fun row : BHist => hsame row exitRead ∧ UnaryHistory row) exitRead := by
    exact ⟨hsame_refl exitRead, exitReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exitRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row exitRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic stream regseq ∧
              Cont regseq realSeal exitRead ∧ PkgSig bundle exitRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exitRead exitReadCarrier
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
      exact ⟨source.right, dyadicStreamRegseq, regseqRealSealExit, exitReadPkg⟩
  }
  exact ⟨cert, exitReadUnary, realSealPkg⟩

theorem MetaCICCriticalPathRealSealNoCompletenessEscape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal escapeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont realSeal provenance escapeRead →
        PkgSig bundle escapeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row escapeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row escapeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle escapeRead pkg ∧
                  PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory escapeRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger sealProvenanceEscape escapePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have escapeUnary : UnaryHistory escapeRead :=
    unary_cont_closed realSealUnary provenanceUnary sealProvenanceEscape
  have escapeSource :
      (fun row : BHist => hsame row escapeRead ∧ UnaryHistory row) escapeRead := by
    exact ⟨hsame_refl escapeRead, escapeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row escapeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row escapeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle escapeRead pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro escapeRead escapeSource
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
      exact ⟨source.right, escapePkg, realSealPkg⟩
  }
  exact ⟨cert, escapeUnary, realSealPkg⟩

theorem MetaCICCriticalPathPhaseRealBudgetExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal exitRead budgetExit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal exitRead →
          Cont exitRead provenance budgetExit →
            PkgSig bundle budgetExit pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row budgetExit ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                      hsame row realSeal ∨ hsame row exitRead ∨ hsame row budgetExit)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont dyadic stream regseq ∧
                      Cont regseq realSeal exitRead ∧ Cont exitRead provenance budgetExit ∧
                        PkgSig bundle budgetExit pkg ∧ PkgSig bundle realSeal pkg)
                  hsame ∧
                UnaryHistory exitRead ∧ UnaryHistory budgetExit ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger dyadicStreamRegseq regseqRealSealExit exitProvenanceBudget budgetPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have exitUnary : UnaryHistory exitRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealExit
  have budgetUnary : UnaryHistory budgetExit :=
    unary_cont_closed exitUnary provenanceUnary exitProvenanceBudget
  have budgetSource :
      (fun row : BHist => hsame row budgetExit ∧ UnaryHistory row) budgetExit := by
    exact ⟨hsame_refl budgetExit, budgetUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetExit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row exitRead ∨ hsame row budgetExit)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dyadic stream regseq ∧
              Cont regseq realSeal exitRead ∧ Cont exitRead provenance budgetExit ∧
                PkgSig bundle budgetExit pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetExit budgetSource
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
      exact
        ⟨source.right, dyadicStreamRegseq, regseqRealSealExit, exitProvenanceBudget,
          budgetPkg, realSealPkg⟩
  }
  exact ⟨cert, exitUnary, budgetUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
