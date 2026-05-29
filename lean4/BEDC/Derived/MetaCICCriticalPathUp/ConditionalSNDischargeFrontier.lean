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

theorem MetaCICCriticalPathConditionalSNDischargeFrontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal frontier auditRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName frontier →
        Cont regseq realSeal auditRead →
          Cont unblock obstruction socketRead →
            PkgSig bundle frontier pkg →
              PkgSig bundle auditRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row frontier ∨ hsame row auditRead ∨ hsame row socketRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row strongNorm ∨ hsame row normalForm ∨
                        hsame row obstruction ∨ hsame row discharge ∨
                          hsame row frontier ∨ hsame row auditRead ∨ hsame row socketRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
                        Cont unblock obstruction socketRead)
                    hsame ∧
                  UnaryHistory frontier ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro ledger continuationLocalFrontier regseqRealAudit unblockObstructionSocket
    frontierPkg _auditPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, _realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalFrontier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed regseqUnary realSealUnary regseqRealAudit
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed unblockUnary obstructionUnary unblockObstructionSocket
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row frontier ∨ hsame row auditRead ∨ hsame row socketRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row discharge ∨ hsame row frontier ∨ hsame row auditRead ∨
                hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontier pkg ∧
              Cont unblock obstruction socketRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontier ⟨Or.inl (hsame_refl frontier), frontierUnary⟩
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
        intro row other sameRows source
        have otherUnary : UnaryHistory other :=
          unary_transport source.right sameRows
        cases source.left with
        | inl sameFrontier =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier), otherUnary⟩
        | inr rest =>
            cases rest with
            | inl sameAudit =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameAudit)),
                    otherUnary⟩
            | inr sameSocket =>
                exact
                  ⟨Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSocket)),
                    otherUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFrontier =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameFrontier))))
      | inr rest =>
          cases rest with
          | inl sameAudit =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameAudit)))))
          | inr sameSocket =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSocket)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, unblockObstructionSocket⟩
  }
  exact ⟨cert, frontierUnary, socketReadUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
