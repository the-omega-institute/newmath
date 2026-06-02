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

theorem MetaCICCriticalPathL10ObjectStatusReadback [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal exactBoundary statusRead closureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont realSeal localName statusRead →
        Cont statusRead provenance closureRead →
          PkgSig bundle closureRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                    hsame row realSeal ∨ hsame row exactBoundary ∨
                      hsame row statusRead ∨ hsame row closureRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle closureRead pkg ∧
                    PkgSig bundle realSeal pkg)
                hsame ∧
              UnaryHistory closureRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger realSealLocalNameStatus statusProvenanceClosure closurePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    _dischargeUnary, _handoffUnary, _continuationUnary, provenanceUnary,
    localNameUnary, _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have statusUnary : UnaryHistory statusRead :=
    unary_cont_closed realSealUnary localNameUnary realSealLocalNameStatus
  have closureUnary : UnaryHistory closureRead :=
    unary_cont_closed statusUnary provenanceUnary statusProvenanceClosure
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
              hsame row realSeal ∨ hsame row exactBoundary ∨ hsame row statusRead ∨
                hsame row closureRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle closureRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro closureRead ⟨hsame_refl closureRead, closureUnary⟩
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
      exact ⟨source.right, closurePkg, realSealPkg⟩
  }
  exact ⟨cert, closureUnary, realSealPkg⟩

end BEDC.Derived.MetaCICCriticalPathUp
