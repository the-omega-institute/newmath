import BEDC.Derived.MetaCICCriticalPathUp

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateMediatedResidualDiamondL10Handoff
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName closedSub residual candidate frontier diamond bounded socket typedBoundary
      l10Read dyadicFace streamFace regSeqFace realFace sourceRead checkerBudget
      combinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg ->
      Cont closedSub residual frontier ->
        Cont frontier candidate diamond ->
          Cont diamond socket bounded ->
            Cont bounded typedBoundary l10Read ->
              Cont l10Read dyadicFace streamFace ->
                Cont streamFace regSeqFace realFace ->
                  Cont realFace localName sourceRead ->
                    Cont route handoff checkerBudget ->
                      Cont checkerBudget dischargeSocket combinedRead ->
                        PkgSig bundle provenance pkg ->
                          PkgSig bundle localName pkg ->
                            PkgSig bundle combinedRead pkg ->
                              UnaryHistory closedSub ->
                                UnaryHistory residual ->
                                  UnaryHistory candidate ->
                                    UnaryHistory socket ->
                                      UnaryHistory typedBoundary ->
                                        UnaryHistory dyadicFace ->
                                          UnaryHistory regSeqFace ->
                                            UnaryHistory localName ->
                                              SemanticNameCert
                                                  (fun row : BHist =>
                                                    hsame row sourceRead ∧
                                                      UnaryHistory row)
                                                  (fun row : BHist =>
                                                    hsame row sourceRead ∨
                                                      hsame row combinedRead ∨
                                                        hsame row l10Read ∨
                                                          hsame row dyadicFace ∨
                                                            hsame row streamFace ∨
                                                              hsame row regSeqFace ∨
                                                                hsame row realFace)
                                                  (fun row : BHist =>
                                                    UnaryHistory row ∧
                                                      PkgSig bundle combinedRead pkg ∧
                                                        PkgSig bundle provenance pkg)
                                                  hsame ∧
                                                UnaryHistory sourceRead ∧
                                                  UnaryHistory combinedRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame
  intro packet closedResidual frontierCandidate diamondSocket boundedTyped l10Dyadic
    streamRegSeq realLocal routeChecker checkerDischarge provenancePkg _localPkg
    combinedPkg closedUnary residualUnary candidateUnary socketUnary typedUnary
    dyadicUnary regSeqUnary localUnary
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary,
    _localNameUnary, _strongNormNormalFormRoute, _handoffObstructionSocket,
    _transportLocalName, _packetProvenancePkg⟩ := packet
  have frontierUnary : UnaryHistory frontier :=
    unary_cont_closed closedUnary residualUnary closedResidual
  have diamondUnary : UnaryHistory diamond :=
    unary_cont_closed frontierUnary candidateUnary frontierCandidate
  have boundedUnary : UnaryHistory bounded :=
    unary_cont_closed diamondUnary socketUnary diamondSocket
  have l10Unary : UnaryHistory l10Read :=
    unary_cont_closed boundedUnary typedUnary boundedTyped
  have streamUnary : UnaryHistory streamFace :=
    unary_cont_closed l10Unary dyadicUnary l10Dyadic
  have realUnary : UnaryHistory realFace :=
    unary_cont_closed streamUnary regSeqUnary streamRegSeq
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed realUnary localUnary realLocal
  have checkerUnary : UnaryHistory checkerBudget :=
    unary_cont_closed routeUnary handoffUnary routeChecker
  have combinedUnary : UnaryHistory combinedRead :=
    unary_cont_closed checkerUnary dischargeSocketUnary checkerDischarge
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row combinedRead ∨ hsame row l10Read ∨
              hsame row dyadicFace ∨ hsame row streamFace ∨ hsame row regSeqFace ∨
                hsame row realFace)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle combinedRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead ⟨hsame_refl sourceRead, sourceUnary⟩
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
      exact Or.inl source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, combinedPkg, provenancePkg⟩
  }
  exact ⟨cert, sourceUnary, combinedUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
