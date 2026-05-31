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

theorem MetaCICCriticalPathBoundedCheckerFrontierSeparation [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead snEndpointRead socketRead
      l10FaceRead checkerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead strongNorm snEndpointRead →
          Cont discharge realSeal socketRead →
            Cont dyadic stream l10FaceRead →
              Cont handoff continuation checkerRead →
                PkgSig bundle l10FaceRead pkg →
                  PkgSig bundle checkerRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row checkerRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row candidateRead ∨ hsame row snEndpointRead ∨
                            hsame row socketRead ∨ hsame row l10FaceRead ∨
                              hsame row checkerRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ PkgSig bundle checkerRead pkg ∧
                            PkgSig bundle realSeal pkg)
                        hsame ∧
                      UnaryHistory candidateRead ∧ UnaryHistory snEndpointRead ∧
                        UnaryHistory socketRead ∧ UnaryHistory l10FaceRead ∧
                          UnaryHistory checkerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateStrongNormEndpoint
    dischargeRealSealSocket dyadicStreamL10 handoffContinuationChecker _l10FacePkg
    checkerPkg
  obtain ⟨packet, dyadicUnary, streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨strongNormUnary, _normalFormUnary, _obstructionUnary, _unblockUnary,
    dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have snEndpointUnary : UnaryHistory snEndpointRead :=
    unary_cont_closed candidateUnary strongNormUnary candidateStrongNormEndpoint
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed dischargeUnary realSealUnary dischargeRealSealSocket
  have l10FaceUnary : UnaryHistory l10FaceRead :=
    unary_cont_closed dyadicUnary streamUnary dyadicStreamL10
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed handoffUnary continuationUnary handoffContinuationChecker
  have checkerSource :
      (fun row : BHist => hsame row checkerRead ∧ UnaryHistory row) checkerRead := by
    exact ⟨hsame_refl checkerRead, checkerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row checkerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row snEndpointRead ∨ hsame row socketRead ∨
              hsame row l10FaceRead ∨ hsame row checkerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle checkerRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro checkerRead checkerSource
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
      exact ⟨source.right, checkerPkg, realSealPkg⟩
  }
  exact
    ⟨cert, candidateUnary, snEndpointUnary, socketUnary, l10FaceUnary, checkerUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
