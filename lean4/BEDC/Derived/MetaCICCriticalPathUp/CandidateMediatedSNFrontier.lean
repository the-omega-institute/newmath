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

theorem MetaCICCriticalPathPacket_candidate_mediated_sn_frontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        PkgSig bundle frontier pkg →
          SemanticNameCert
              (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row unblock ∨ hsame row discharge ∨ hsame row handoff ∨
                    hsame row continuation ∨ hsame row dyadic ∨ hsame row stream ∨
                      hsame row regseq ∨ hsame row realSeal ∨ hsame row frontier)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle frontier pkg ∧ PkgSig bundle realSeal pkg)
              hsame ∧
            UnaryHistory frontier ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier frontierPkg
  obtain ⟨packet, dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have sourceFrontier :
      (fun row : BHist => hsame row frontier ∧ UnaryHistory row) frontier := by
    exact ⟨hsame_refl frontier, frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontier ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row unblock ∨ hsame row discharge ∨ hsame row handoff ∨
                hsame row continuation ∨ hsame row dyadic ∨ hsame row stream ∨
                  hsame row regseq ∨ hsame row realSeal ∨ hsame row frontier)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontier pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontier sourceFrontier
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, realSealPkg⟩
  }
  exact ⟨cert, frontierUnary, realSealPkg⟩

theorem MetaCICCriticalPathCandidateMediatedFrontierSocketSeparation [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont unblock obstruction socketRead →
          PkgSig bundle frontier pkg →
            SemanticNameCert
                (fun row : BHist => (hsame row frontier ∨ hsame row socketRead) ∧
                  UnaryHistory row)
                (fun row : BHist =>
                  hsame row obstruction ∨ hsame row discharge ∨ hsame row frontier ∨
                    hsame row socketRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
                    Cont unblock obstruction socketRead)
                hsame ∧
              UnaryHistory frontier ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier unblockObstructionRead frontierPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed unblockUnary obstructionUnary unblockObstructionRead
  have sourceFrontier :
      (fun row : BHist => (hsame row frontier ∨ hsame row socketRead) ∧
        UnaryHistory row) frontier := by
    exact ⟨Or.inl (hsame_refl frontier), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => (hsame row frontier ∨ hsame row socketRead) ∧
            UnaryHistory row)
          (fun row : BHist =>
            hsame row obstruction ∨ hsame row discharge ∨ hsame row frontier ∨
              hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
              Cont unblock obstruction socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontier sourceFrontier
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        constructor
        · cases source.left with
          | inl sameFrontier =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier)
          | inr sameSocket =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameSocket)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFrontier =>
          exact Or.inr (Or.inr (Or.inl sameFrontier))
      | inr sameSocket =>
          exact Or.inr (Or.inr (Or.inr sameSocket))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, unblockObstructionRead⟩
  }
  exact ⟨cert, frontierUnary, socketReadUnary⟩

theorem MetaCICCriticalPathSNConfluenceDecidabilityHandshake [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName handshakeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm handoff handshakeRead →
        PkgSig bundle handshakeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row handshakeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row handoff ∨
                  hsame row route ∨ hsame row handshakeRead)
              (fun row : BHist =>
                hsame row handshakeRead ∧ PkgSig bundle handshakeRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory handshakeRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro packet strongNormHandoffRead handshakeReadPkg
  obtain ⟨strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have handshakeUnary : UnaryHistory handshakeRead :=
    unary_cont_closed strongNormUnary handoffUnary strongNormHandoffRead
  have sourceHandshake :
      (fun row : BHist => hsame row handshakeRead ∧ UnaryHistory row) handshakeRead := by
    exact ⟨hsame_refl handshakeRead, handshakeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handshakeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row handoff ∨
              hsame row route ∨ hsame row handshakeRead)
          (fun row : BHist =>
            hsame row handshakeRead ∧ PkgSig bundle handshakeRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handshakeRead sourceHandshake
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
      exact ⟨source.left, handshakeReadPkg, provenancePkg⟩
  }
  exact ⟨cert, handshakeUnary, provenancePkg⟩

theorem MetaCICCriticalPathCandidateMediatedFrontierHandoffTotality [AskSetup]
    [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont frontier handoff handoffRead →
          PkgSig bundle handoffRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row frontier ∨ hsame row handoff ∨ hsame row handoffRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle handoffRead pkg ∧
                    Cont frontier handoff handoffRead)
                hsame ∧
              UnaryHistory frontier ∧ UnaryHistory handoffRead ∧
                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier frontierHandoffRead handoffReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed frontierUnary handoffUnary frontierHandoffRead
  have sourceHandoffRead :
      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row) handoffRead := by
    exact ⟨hsame_refl handoffRead, handoffReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row handoff ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle handoffRead pkg ∧
              Cont frontier handoff handoffRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead sourceHandoffRead
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
      exact ⟨source.right, handoffReadPkg, frontierHandoffRead⟩
  }
  exact ⟨cert, frontierUnary, handoffReadUnary, realSealPkg⟩

theorem MetaCICCriticalPathCandidateMediatedSNDischargeBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier dischargeRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont frontier discharge dischargeRead →
          Cont dischargeRead handoff budgetRead →
            PkgSig bundle budgetRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row frontier ∨ hsame row discharge ∨ hsame row obstruction ∨
                      hsame row budgetRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ PkgSig bundle budgetRead pkg ∧
                      Cont dischargeRead handoff budgetRead)
                  hsame ∧
                UnaryHistory dischargeRead ∧ UnaryHistory budgetRead ∧
                  PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalFrontier frontierDischargeRead dischargeHandoffBudget
    budgetReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, _realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have dischargeReadUnary : UnaryHistory dischargeRead :=
    unary_cont_closed frontierUnary dischargeUnary frontierDischargeRead
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed dischargeReadUnary _handoffUnary dischargeHandoffBudget
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row frontier ∨ hsame row discharge ∨ hsame row obstruction ∨
              hsame row budgetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle budgetRead pkg ∧
              Cont dischargeRead handoff budgetRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, budgetReadPkg, dischargeHandoffBudget⟩
  }
  exact ⟨cert, dischargeReadUnary, budgetReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
