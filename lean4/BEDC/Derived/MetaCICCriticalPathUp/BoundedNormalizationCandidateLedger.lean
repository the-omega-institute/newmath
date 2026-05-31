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

theorem MetaCICCriticalPathBoundedNormalizationCandidateLedger [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal boundedCandidate boundedLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName boundedCandidate →
        Cont boundedCandidate realSeal boundedLedger →
          PkgSig bundle boundedLedger pkg →
            SemanticNameCert
                (fun row : BHist => hsame row boundedLedger ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row continuation ∨ hsame row localName ∨
                    hsame row boundedCandidate ∨ hsame row realSeal ∨
                      hsame row boundedLedger)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle boundedLedger pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory boundedCandidate ∧ UnaryHistory boundedLedger ∧
                PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateRealSealLedger boundedLedgerPkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have boundedCandidateUnary : UnaryHistory boundedCandidate :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have boundedLedgerUnary : UnaryHistory boundedLedger :=
    unary_cont_closed boundedCandidateUnary realSealUnary candidateRealSealLedger
  have sourceLedger :
      (fun row : BHist => hsame row boundedLedger ∧ UnaryHistory row)
        boundedLedger := by
    exact ⟨hsame_refl boundedLedger, boundedLedgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundedLedger ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row continuation ∨ hsame row localName ∨
              hsame row boundedCandidate ∨ hsame row realSeal ∨
                hsame row boundedLedger)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle boundedLedger pkg ∧
              PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundedLedger sourceLedger
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
      exact ⟨source.right, boundedLedgerPkg, realSealPkg⟩
  }
  exact ⟨cert, boundedCandidateUnary, boundedLedgerUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
