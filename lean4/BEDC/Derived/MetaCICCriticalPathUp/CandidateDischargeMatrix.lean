import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathCandidateDischargeMatrix [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead residualRead checkerRead
      dischargeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead realSeal residualRead →
          Cont residualRead obstruction checkerRead →
            Cont checkerRead discharge dischargeRead →
              PkgSig bundle dischargeRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row candidateRead ∨ hsame row residualRead ∨
                          hsame row checkerRead ∨ hsame row dischargeRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                        hsame row realSeal ∨ hsame row candidateRead ∨
                          hsame row residualRead ∨ hsame row checkerRead ∨
                            hsame row dischargeRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧
                        PkgSig bundle dischargeRead pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                    UnaryHistory checkerRead ∧ UnaryHistory dischargeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro ledger continuationLocalNameCandidate candidateRealResidual
    residualObstructionChecker checkerDischargeRead dischargePkg
  obtain ⟨packet, _dyadicUnary, _streamUnary, _regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    dischargeUnary, _handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge, _handoffLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary realSealUnary candidateRealResidual
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionChecker
  have dischargeUnaryRead : UnaryHistory dischargeRead :=
    unary_cont_closed checkerUnary dischargeUnary checkerDischargeRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row candidateRead ∨ hsame row residualRead ∨ hsame row checkerRead ∨
                hsame row dischargeRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨ hsame row realSeal ∨
              hsame row candidateRead ∨ hsame row residualRead ∨ hsame row checkerRead ∨
                hsame row dischargeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle realSeal pkg ∧ PkgSig bundle dischargeRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro dischargeRead
          ⟨Or.inr (Or.inr (Or.inr (hsame_refl dischargeRead))), dischargeUnaryRead⟩
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
        have transportedUnary : UnaryHistory _ := unary_transport source.right sameRows
        cases source.left with
        | inl sameCandidate =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameCandidate),
                transportedUnary⟩
        | inr rest =>
            cases rest with
            | inl sameResidual =>
                exact
                  ⟨Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameResidual)),
                    transportedUnary⟩
            | inr rest =>
                cases rest with
                | inl sameChecker =>
                    exact
                      ⟨Or.inr (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameChecker))),
                        transportedUnary⟩
                | inr sameDischarge =>
                    exact
                      ⟨Or.inr (Or.inr
                        (Or.inr (hsame_trans (hsame_symm sameRows) sameDischarge))),
                        transportedUnary⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCandidate =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameCandidate))))
      | inr rest =>
          cases rest with
          | inl sameResidual =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameResidual)))))
          | inr rest =>
              cases rest with
              | inl sameChecker =>
                  exact
                    Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inl sameChecker))))))
              | inr sameDischarge =>
                  exact
                    Or.inr (Or.inr (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr sameDischarge))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, realSealPkg, dischargePkg⟩
  }
  exact ⟨cert, candidateUnary, residualUnary, checkerUnary, dischargeUnaryRead⟩

theorem MetaCICCriticalPathL10CandidateSocketExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead residualRead checkerRead dyadicRead streamRead regseqRead
      realRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName candidateRead →
        Cont candidateRead handoff residualRead →
          Cont residualRead obstruction checkerRead →
            Cont checkerRead dischargeSocket socketRead →
              PkgSig bundle socketRead pkg →
                PkgSig bundle realRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row residualRead ∨
                          hsame row checkerRead ∨ hsame row dyadicRead ∨
                            hsame row streamRead ∨ hsame row regseqRead ∨
                              hsame row realRead ∨ hsame row socketRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont route localName candidateRead ∧
                          Cont candidateRead handoff residualRead ∧
                            Cont residualRead obstruction checkerRead ∧
                              Cont checkerRead dischargeSocket socketRead ∧
                                PkgSig bundle socketRead pkg)
                      hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                      UnaryHistory checkerRead ∧ UnaryHistory socketRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameCandidate candidateHandoffResidual residualObstructionChecker
    checkerSocket socketPkg _realPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    socketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffResidual
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionChecker
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed checkerUnary socketUnary checkerSocket
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row socketRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row residualRead ∨ hsame row checkerRead ∨
              hsame row dyadicRead ∨ hsame row streamRead ∨ hsame row regseqRead ∨
                hsame row realRead ∨ hsame row socketRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route localName candidateRead ∧
              Cont candidateRead handoff residualRead ∧
                Cont residualRead obstruction checkerRead ∧
                  Cont checkerRead dischargeSocket socketRead ∧ PkgSig bundle socketRead pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeLocalNameCandidate, candidateHandoffResidual,
          residualObstructionChecker, checkerSocket, socketPkg⟩
  }
  exact ⟨cert, candidateUnary, residualUnary, checkerUnary, socketReadUnary⟩

theorem MetaCICCriticalPathCandidateDischargeMatrixFrontier [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead residualRead checkerRead dyadicRead streamRead regseqRead
      realRead socketRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName candidateRead →
        Cont candidateRead handoff residualRead →
          Cont residualRead obstruction checkerRead →
            Cont checkerRead dischargeSocket socketRead →
              Cont socketRead provenance frontierRead →
                PkgSig bundle socketRead pkg →
                  PkgSig bundle frontierRead pkg →
                    PkgSig bundle realRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row candidateRead ∨ hsame row residualRead ∨
                              hsame row checkerRead ∨ hsame row socketRead ∨
                                hsame row frontierRead ∨ hsame row dyadicRead ∨
                                  hsame row streamRead ∨ hsame row regseqRead ∨
                                    hsame row realRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont checkerRead dischargeSocket socketRead ∧
                              Cont socketRead provenance frontierRead ∧
                                PkgSig bundle frontierRead pkg)
                          hsame ∧
                        UnaryHistory socketRead ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameCandidate candidateHandoffResidual residualObstructionChecker
    checkerSocket socketProvenanceFrontier _socketPkg frontierPkg _realPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    socketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffResidual
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionChecker
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed checkerUnary socketUnary checkerSocket
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed socketReadUnary provenanceUnary socketProvenanceFrontier
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row residualRead ∨ hsame row checkerRead ∨
              hsame row socketRead ∨ hsame row frontierRead ∨ hsame row dyadicRead ∨
                hsame row streamRead ∨ hsame row regseqRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont checkerRead dischargeSocket socketRead ∧
              Cont socketRead provenance frontierRead ∧ PkgSig bundle frontierRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inl source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, checkerSocket, socketProvenanceFrontier, frontierPkg⟩
  }
  exact ⟨cert, socketReadUnary, frontierUnary⟩

theorem MetaCICCriticalPathRetainedPremiseDischargeBoundary [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName candidateRead residualRead checkerRead retainedRead dyadicRead streamRead
      regseqRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName candidateRead →
        Cont candidateRead handoff residualRead →
          Cont residualRead obstruction checkerRead →
            Cont checkerRead dischargeSocket retainedRead →
              PkgSig bundle retainedRead pkg →
                PkgSig bundle realRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row candidateRead ∨ hsame row residualRead ∨
                          hsame row checkerRead ∨ hsame row retainedRead ∨
                            hsame row dyadicRead ∨ hsame row streamRead ∨
                              hsame row regseqRead ∨ hsame row realRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont checkerRead dischargeSocket retainedRead ∧
                          PkgSig bundle retainedRead pkg)
                      hsame ∧
                    UnaryHistory candidateRead ∧ UnaryHistory residualRead ∧
                      UnaryHistory checkerRead ∧ UnaryHistory retainedRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle SemanticNameCert hsame UnaryHistory
  intro packet routeLocalNameCandidate candidateHandoffResidual residualObstructionChecker
    checkerRetained retainedPkg _realPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    socketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameCandidate
  have residualUnary : UnaryHistory residualRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffResidual
  have checkerUnary : UnaryHistory checkerRead :=
    unary_cont_closed residualUnary obstructionUnary residualObstructionChecker
  have retainedUnary : UnaryHistory retainedRead :=
    unary_cont_closed checkerUnary socketUnary checkerRetained
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row retainedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row residualRead ∨ hsame row checkerRead ∨
              hsame row retainedRead ∨ hsame row dyadicRead ∨ hsame row streamRead ∨
                hsame row regseqRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont checkerRead dischargeSocket retainedRead ∧
              PkgSig bundle retainedRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro retainedRead ⟨hsame_refl retainedRead, retainedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, checkerRetained, retainedPkg⟩
  }
  exact ⟨cert, candidateUnary, residualUnary, checkerUnary, retainedUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
