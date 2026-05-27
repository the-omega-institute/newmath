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

theorem MetaCICCriticalPathConfluenceDecidabilityHandoffExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket transport
        route provenance localName bundle pkg →
      Cont handoff obstruction socketRead →
        PkgSig bundle socketRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                    hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                      hsame row socketRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                  Cont handoff obstruction socketRead)
              hsame ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro packet handoffObstructionRead socketReadPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    _dischargeSocketUnary, _transportUnary, _routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, provenancePkg⟩ := packet
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row localName ∨
                  hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              Cont handoff obstruction socketRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro socketRead ⟨hsame_refl socketRead, socketReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, socketReadPkg, handoffObstructionRead⟩
  }
  exact ⟨cert, provenancePkg⟩

theorem MetaCICCriticalPathCandidateSNFourFaceAuditPrecondition [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont dyadic stream regseq →
        Cont regseq realSeal auditRead →
          PkgSig bundle auditRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row auditRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory auditRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger _dyadicStreamRegseq regseqRealSealAudit auditReadPkg
  obtain ⟨_packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _ledgerDyadicStreamRegseq, _ledgerRegseqRealSealHandoff, realSealPkg⟩ := ledger
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row auditRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro auditRead ⟨hsame_refl auditRead, auditReadUnary⟩
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
      exact ⟨source.right, auditReadPkg, realSealPkg⟩
  }
  exact ⟨cert, auditReadUnary, realSealPkg⟩

theorem MetaCICCriticalPathCandidateSNSocketNonescape [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont discharge realSeal socketRead →
        PkgSig bundle socketRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                  hsame row realSeal ∨ hsame row discharge ∨ hsame row socketRead)
              (fun row : BHist =>
                PkgSig bundle socketRead pkg ∧ PkgSig bundle realSeal pkg ∧
                  hsame row socketRead)
              hsame ∧
            UnaryHistory discharge ∧ UnaryHistory socketRead ∧
              PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger dischargeRealSealSocket socketReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed dischargeUnary realSealUnary dischargeRealSealSocket
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row discharge ∨ hsame row socketRead)
          (fun row : BHist =>
            PkgSig bundle socketRead pkg ∧ PkgSig bundle realSeal pkg ∧
              hsame row socketRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro socketRead ⟨hsame_refl socketRead, socketReadUnary⟩
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
      exact ⟨socketReadPkg, realSealPkg, source.left⟩
  }
  exact ⟨cert, dischargeUnary, socketReadUnary, realSealPkg⟩

theorem MetaCICCriticalPathFourFaceDischargePreconditionStrengthening
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal auditRead dischargeBoundary : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont regseq realSeal auditRead →
        Cont discharge auditRead dischargeBoundary →
          PkgSig bundle auditRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row dischargeBoundary ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row discharge ∨ hsame row auditRead ∨
                    hsame row dischargeBoundary)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧
                    Cont discharge auditRead dischargeBoundary)
                hsame ∧
              UnaryHistory dischargeBoundary ∧ UnaryHistory discharge := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger regseqRealSealAudit dischargeAuditBoundary auditReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealSealAudit
  have dischargeBoundaryUnary : UnaryHistory dischargeBoundary :=
    unary_cont_closed dischargeUnary auditReadUnary dischargeAuditBoundary
  have boundaryCarrier :
      (fun row : BHist => hsame row dischargeBoundary ∧ UnaryHistory row)
        dischargeBoundary := by
    exact ⟨hsame_refl dischargeBoundary, dischargeBoundaryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row dischargeBoundary ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row discharge ∨ hsame row auditRead ∨ hsame row dischargeBoundary)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle auditRead pkg ∧
              Cont discharge auditRead dischargeBoundary)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro dischargeBoundary boundaryCarrier
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
      exact ⟨source.right, auditReadPkg, dischargeAuditBoundary⟩
  }
  exact ⟨cert, dischargeBoundaryUnary, dischargeUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
