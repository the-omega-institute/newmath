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

theorem MetaCICCriticalPathCandidateSNFiniteSocketNormalForm [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal auditRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont regseq realSeal auditRead →
        Cont discharge auditRead socketRead →
          PkgSig bundle socketRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row discharge ∨ hsame row auditRead ∨ hsame row socketRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
                    Cont discharge auditRead socketRead)
                hsame ∧
              UnaryHistory auditRead ∧ UnaryHistory socketRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro ledger regseqSealAudit dischargeAuditSocket socketReadPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, _continuationUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed regseqUnary realSealUnary regseqSealAudit
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed dischargeUnary auditReadUnary dischargeAuditSocket
  have sourceSocket :
      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row) socketRead := by
    exact ⟨hsame_refl socketRead, socketReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row discharge ∨ hsame row auditRead ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle socketRead pkg ∧
              Cont discharge auditRead socketRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro socketRead sourceSocket
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
      exact ⟨source.right, socketReadPkg, dischargeAuditSocket⟩
  }
  exact ⟨cert, auditReadUnary, socketReadUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
