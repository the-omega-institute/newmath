import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetaCICCriticalPathPacket [AskSetup] [PackageSetup]
    (strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory strongNorm ∧ UnaryHistory normalForm ∧ UnaryHistory obstruction ∧
    UnaryHistory handoff ∧ UnaryHistory dischargeSocket ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont strongNorm normalForm route ∧ Cont handoff obstruction dischargeSocket ∧
          hsame transport localName ∧ PkgSig bundle provenance pkg

theorem MetaCICCriticalPathPacket_consistency_handoff [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont strongNorm normalForm route ∧ hsame transport localName ∧
        PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont PkgSig ProbeBundle UnaryHistory
  intro packet
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _socketUnary, _transportUnary, _routeUnary, _provenanceUnary, _localNameUnary,
    strongNormNormalFormRoute, _handoffObstructionSocket, transportLocalName,
    provenancePkg⟩ := packet
  exact ⟨strongNormNormalFormRoute, transportLocalName, provenancePkg⟩

theorem MetaCICCriticalPathDischargeSocketNonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff obstruction socketRead →
        PkgSig bundle socketRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row handoff ∨ hsame row obstruction ∨ hsame row socketRead)
              (fun row : BHist => hsame row socketRead ∧ PkgSig bundle socketRead pkg)
              hsame ∧
            UnaryHistory socketRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet handoffObstructionRead socketReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionRead
  have sourceSocketRead :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row obstruction ∨ hsame row socketRead)
          (fun row : BHist => hsame row socketRead ∧ PkgSig bundle socketRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocketRead
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
      exact ⟨source.left, socketReadPkg⟩
  }
  exact ⟨cert, socketReadUnary, provenancePkg⟩

private theorem MetaCICCriticalPathDyadicRatCoreBudgetReadiness_budget_unary
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        UnaryHistory dyadicBudget := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro packet routeLocalNameBudget
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  exact unary_cont_closed routeUnary localNameUnary routeLocalNameBudget

theorem MetaCICCriticalPathDyadicRatCoreBudgetReadiness [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        PkgSig bundle dyadicBudget pkg →
          SemanticNameCert
              (fun row : BHist => hsame row dyadicBudget ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row route ∨ hsame row localName ∨ hsame row dyadicBudget)
              (fun row : BHist =>
                hsame row dyadicBudget ∧ PkgSig bundle dyadicBudget pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory dyadicBudget ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameBudget dyadicBudgetPkg
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    MetaCICCriticalPathDyadicRatCoreBudgetReadiness_budget_unary packet routeLocalNameBudget
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have sourceDyadicBudget :
      (fun row : BHist => hsame row dyadicBudget ∧ UnaryHistory row) dyadicBudget := by
    exact ⟨hsame_refl dyadicBudget, dyadicBudgetUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dyadicBudget ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row localName ∨ hsame row dyadicBudget)
          (fun row : BHist =>
            hsame row dyadicBudget ∧ PkgSig bundle dyadicBudget pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dyadicBudget sourceDyadicBudget
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
      exact ⟨source.left, dyadicBudgetPkg, provenancePkg⟩
  }
  exact ⟨cert, dyadicBudgetUnary, provenancePkg⟩

theorem MetaCICCriticalPathPacket_provenance_nonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName provenanceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont provenance localName provenanceRead →
        PkgSig bundle provenanceRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row provenanceRead ∧ UnaryHistory row ∧
                PkgSig bundle row pkg)
              (fun row : BHist => Cont provenance localName row ∧ hsame transport localName)
              (fun row : BHist =>
                PkgSig bundle row pkg ∧ Cont strongNorm normalForm route ∧
                  Cont handoff obstruction dischargeSocket)
              hsame ∧
            UnaryHistory provenanceRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet provenanceLocalNameRead provenanceReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, provenanceUnary, localNameUnary,
    strongNormNormalFormRoute, handoffObstructionSocket, transportLocalName, provenancePkg⟩ :=
    packet
  have provenanceReadUnary : UnaryHistory provenanceRead :=
    unary_cont_closed provenanceUnary localNameUnary provenanceLocalNameRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row provenanceRead ∧ UnaryHistory row ∧
            PkgSig bundle row pkg)
          (fun row : BHist => Cont provenance localName row ∧ hsame transport localName)
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ Cont strongNorm normalForm route ∧
              Cont handoff obstruction dischargeSocket)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro provenanceRead
          ⟨hsame_refl provenanceRead, provenanceReadUnary, provenanceReadPkg⟩
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨cont_result_hsame_transport provenanceLocalNameRead (hsame_symm source.left),
          transportLocalName⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, strongNormNormalFormRoute, handoffObstructionSocket⟩
  }
  exact ⟨cert, provenanceReadUnary, provenancePkg⟩

theorem MetaCICCriticalPathL10FourObjectExitCertificate [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName dyadicBudget streamSchedule regReadback realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName dyadicBudget →
        Cont dyadicBudget route streamSchedule →
          Cont streamSchedule normalForm regReadback →
            Cont regReadback provenance realSeal →
              PkgSig bundle realSeal pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row dyadicBudget ∨ hsame row streamSchedule ∨
                        hsame row regReadback ∨ hsame row realSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧
                        PkgSig bundle provenance pkg)
                    hsame ∧
                  UnaryHistory realSeal ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameBudget budgetRouteSchedule scheduleNormalFormReadback
    readbackProvenanceSeal realSealPkg
  obtain ⟨_strongNormUnary, normalFormUnary, _obstructionUnary, _handoffUnary,
    _dischargeSocketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have dyadicBudgetUnary : UnaryHistory dyadicBudget :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameBudget
  have streamScheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed dyadicBudgetUnary routeUnary budgetRouteSchedule
  have regReadbackUnary : UnaryHistory regReadback :=
    unary_cont_closed streamScheduleUnary normalFormUnary scheduleNormalFormReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed regReadbackUnary provenanceUnary readbackProvenanceSeal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicBudget ∨ hsame row streamSchedule ∨
              hsame row regReadback ∨ hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
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
      exact ⟨source.right, realSealPkg, provenancePkg⟩
  }
  exact ⟨cert, realSealUnary, provenancePkg⟩

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

end BEDC.Derived.MetaCICCriticalPathUp
