import BEDC.Derived.MetaCICCriticalPathUp.Core

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICCriticalPathOpenPhaseSourceLedger [AskSetup] [PackageSetup]
    (strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  MetaCICCriticalPathPacket strongNorm normalForm obstruction unblock discharge handoff
      continuation provenance localName bundle pkg ∧
    UnaryHistory dyadic ∧ UnaryHistory stream ∧ UnaryHistory regseq ∧
      UnaryHistory realSeal ∧ Cont dyadic stream regseq ∧ Cont regseq realSeal handoff ∧
        PkgSig bundle realSeal pkg

theorem MetaCICCriticalPathOpenPhaseSourceClosure [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal sourceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      (hsame sourceRead dyadic ∨ hsame sourceRead stream ∨ hsame sourceRead regseq ∨
          hsame sourceRead realSeal) →
        SemanticNameCert
            (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
            (fun row : BHist =>
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal)
            (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row sourceRead)
            hsame ∧
          PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro ledger sourceCase
  obtain ⟨_packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  have sourceReadUnary : UnaryHistory sourceRead := by
    cases sourceCase with
    | inl sourceDyadic =>
        exact unary_transport dyadicUnary (hsame_symm sourceDyadic)
    | inr rest =>
        cases rest with
        | inl sourceStream =>
            exact unary_transport streamUnary (hsame_symm sourceStream)
        | inr rest =>
            cases rest with
            | inl sourceRegseq =>
                exact unary_transport regseqUnary (hsame_symm sourceRegseq)
            | inr sourceRealSeal =>
                exact unary_transport realSealUnary (hsame_symm sourceRealSeal)
  have sourceWitness :
      (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row) sourceRead := by
    exact ⟨hsame_refl sourceRead, sourceReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨ hsame row realSeal)
          (fun row : BHist => PkgSig bundle realSeal pkg ∧ hsame row sourceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceWitness
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
      cases sourceCase with
      | inl sourceDyadic =>
          exact Or.inl (hsame_trans source.left sourceDyadic)
      | inr rest =>
          cases rest with
          | inl sourceStream =>
              exact Or.inr (Or.inl (hsame_trans source.left sourceStream))
          | inr rest =>
              cases rest with
              | inl sourceRegseq =>
                  exact Or.inr (Or.inr (Or.inl (hsame_trans source.left sourceRegseq)))
              | inr sourceRealSeal =>
                  exact Or.inr (Or.inr (Or.inr (hsame_trans source.left sourceRealSeal)))
    ledger_sound := by
      intro _row source
      exact ⟨realSealPkg, source.left⟩
  }
  exact ⟨cert, realSealPkg⟩

theorem MetaCICCriticalPathCandidateMediatedSNRoute [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName confluenceRead →
        PkgSig bundle confluenceRead pkg →
          UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧ UnaryHistory obstruction ∧
            UnaryHistory discharge ∧ UnaryHistory dyadic ∧ UnaryHistory stream ∧
              UnaryHistory regseq ∧ UnaryHistory realSeal ∧ UnaryHistory confluenceRead ∧
                Cont strongNorm normalForm continuation ∧
                  Cont continuation localName confluenceRead ∧ PkgSig bundle realSeal pkg ∧
                    PkgSig bundle confluenceRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro ledger continuationLocalNameRead confluenceReadPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary, localNameUnary,
    strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have confluenceReadUnary : UnaryHistory confluenceRead :=
    unary_cont_closed _continuationUnary localNameUnary continuationLocalNameRead
  exact
    ⟨strongNormUnary, normalFormUnary, obstructionUnary, dischargeUnary, dyadicUnary,
      streamUnary, regseqUnary, realSealUnary, confluenceReadUnary,
      strongNormNormalFormContinuation, continuationLocalNameRead, realSealPkg,
      confluenceReadPkg⟩

theorem MetaCICCriticalPathCandidateMediatedFrontierL10Readback [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier l10Read : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont frontier realSeal l10Read →
          PkgSig bundle l10Read pkg →
            SemanticNameCert
                (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row obstruction ∨ hsame row discharge ∨
                      hsame row l10Read)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle l10Read pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory l10Read ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameFrontier frontierRealSealReadback l10ReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameFrontier
  have l10ReadUnary : UnaryHistory l10Read :=
    unary_cont_closed frontierUnary realSealUnary frontierRealSealReadback
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row l10Read ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row obstruction ∨ hsame row discharge ∨
                hsame row l10Read)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle l10Read pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro l10Read ⟨hsame_refl l10Read, l10ReadUnary⟩
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
      exact ⟨source.right, l10ReadPkg, realSealPkg⟩
  }
  exact ⟨cert, l10ReadUnary, realSealPkg⟩

theorem MetaCICCriticalPathRealSealFrontierExactness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regRead realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        Cont dyadicBudget route streamSchedule →
          Cont streamSchedule provenance regRead →
            Cont regRead localName realSeal →
              PkgSig bundle realSeal pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                        hsame row regRead ∨ hsame row realSeal)
                    (fun row : BHist => UnaryHistory row)
                    (fun row : BHist =>
                      PkgSig bundle provenance pkg ∨ PkgSig bundle row pkg)
                    hsame ∧
                  UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleProvenanceRead
    readLocalNameSeal _realSealPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicBudgetUnary routeUnary budgetRouteSchedule
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed streamScheduleUnary provenanceUnary scheduleProvenanceRead
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadUnary localNameUnary readLocalNameSeal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨ hsame row regRead ∨
              hsame row realSeal)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => PkgSig bundle provenance pkg ∨ PkgSig bundle row pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dyadicBudget (Or.inl (hsame_refl dyadicBudget))
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
        cases source with
        | inl sameBudget =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameBudget)
        | inr rest =>
            cases rest with
            | inl sameSchedule =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSchedule))
            | inr rest =>
                cases rest with
                | inl sameRead =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameRead)))
                | inr sameSeal =>
                    exact Or.inr (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSeal)))
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameBudget =>
          exact unary_transport dyadicBudgetUnary (hsame_symm sameBudget)
      | inr rest =>
          cases rest with
          | inl sameSchedule =>
              exact unary_transport streamScheduleUnary (hsame_symm sameSchedule)
          | inr rest =>
              cases rest with
              | inl sameRead =>
                  exact unary_transport regReadUnary (hsame_symm sameRead)
              | inr sameSeal =>
                  exact unary_transport realSealUnary (hsame_symm sameSeal)
    ledger_sound := by
      intro _row _source
      exact Or.inl provenancePkg
  }
  exact ⟨cert, realSealUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
