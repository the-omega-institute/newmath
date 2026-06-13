import BEDC.Derived.MetaCICCriticalPathUp.Core
import BEDC.Derived.MetaCICCriticalPathUp.CandidateMediatedSNBoundedDischargeRoute
import BEDC.Derived.MetaCICCriticalPathUp.CandidateSNConfluenceHandoff
import BEDC.Derived.MetaCICCriticalPathUp.CandidateSNHandoffSourceExhaustion
import BEDC.Derived.MetaCICCriticalPathUp.FrontierCompanion
import BEDC.Derived.MetaCICCriticalPathUp.MatureConsumerSynthesis
import BEDC.Derived.MetaCICCriticalPathUp.MaturePackageConsumer
import BEDC.Derived.MetaCICCriticalPathUp.NormalizationConsumerHandoff
import BEDC.Derived.MetaCICCriticalPathUp.OpenPhase
import BEDC.Derived.MetaCICCriticalPathUp.ParallelDiamondFrontierSeed
import BEDC.Derived.MetaCICCriticalPathUp.PhaseRealNormalFormHandoff
import BEDC.Derived.MetaCICCriticalPathUp.ResidualBudgetBridge
import BEDC.Derived.MetaCICCriticalPathUp.ResidualDiamondCompletionNonescape
import BEDC.Derived.MetaCICCriticalPathUp.ResidualDiamondVisibleRoute
import BEDC.Derived.MetaCICCriticalPathUp.ResidualSocketBeforeSNRead
import BEDC.Derived.MetaCICCriticalPathUp.ResidualSocketConsumerSurface

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathPublicRouteCertificate [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                  hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                    hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet routeLocalNamePublic publicPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _socketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNamePublic
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle publicRead pkg ∧
              PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      exact ⟨source.right, publicPkg, provenancePkg⟩
  }
  exact ⟨cert, publicUnary⟩

theorem MetaCICCriticalPathPhaseRealRouteBudget [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName streamSchedule regSeqReadback realSeal phaseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName streamSchedule →
        Cont streamSchedule localName regSeqReadback →
          Cont regSeqReadback localName realSeal →
            Cont realSeal provenance phaseRead →
              PkgSig bundle phaseRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row route ∨ hsame row streamSchedule ∨
                        hsame row regSeqReadback ∨ hsame row realSeal ∨
                          hsame row phaseRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont route localName streamSchedule ∧
                        Cont streamSchedule localName regSeqReadback ∧
                          Cont regSeqReadback localName realSeal ∧
                            Cont realSeal provenance phaseRead ∧
                              PkgSig bundle phaseRead pkg)
                    hsame ∧
                  UnaryHistory phaseRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet routeLocalNameSchedule scheduleLocalNameReadback readbackLocalNameSeal
    sealProvenancePhase phasePkg
  obtain ⟨_strongNormUnary, _normalFormUnary, _obstructionUnary, _handoffUnary,
    _socketUnary, _transportUnary, routeUnary, provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have scheduleUnary : UnaryHistory streamSchedule :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameSchedule
  have readbackUnary : UnaryHistory regSeqReadback :=
    unary_cont_closed scheduleUnary localNameUnary scheduleLocalNameReadback
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readbackUnary localNameUnary readbackLocalNameSeal
  have phaseUnary : UnaryHistory phaseRead :=
    unary_cont_closed realSealUnary provenanceUnary sealProvenancePhase
  have sourcePhase :
      (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row) phaseRead := by
    exact ⟨hsame_refl phaseRead, phaseUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row phaseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row route ∨ hsame row streamSchedule ∨ hsame row regSeqReadback ∨
              hsame row realSeal ∨ hsame row phaseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route localName streamSchedule ∧
              Cont streamSchedule localName regSeqReadback ∧
                Cont regSeqReadback localName realSeal ∧
                  Cont realSeal provenance phaseRead ∧ PkgSig bundle phaseRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro phaseRead sourcePhase
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
      exact
        ⟨source.right, routeLocalNameSchedule, scheduleLocalNameReadback,
          readbackLocalNameSeal, sealProvenancePhase, phasePkg⟩
  }
  exact ⟨cert, phaseUnary, provenancePkg⟩

theorem MetaCICCriticalPathCandidateMediatedSNFrontierDischarge
    [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction unblock discharge handoff continuation provenance
      localName dyadic stream regseq realSeal candidateRead frontierRead socketRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathOpenPhaseSourceLedger strongNorm normalForm obstruction unblock
        discharge handoff continuation provenance localName dyadic stream regseq realSeal
        bundle pkg →
      Cont continuation localName candidateRead →
        Cont candidateRead handoff frontierRead →
          Cont frontierRead obstruction socketRead →
            PkgSig bundle frontierRead pkg →
              PkgSig bundle socketRead pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row frontierRead ∨ hsame row socketRead ∨
                        hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                          hsame row realSeal) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row candidateRead ∨ hsame row frontierRead ∨
                        hsame row socketRead ∨ hsame row dyadic ∨ hsame row stream ∨
                          hsame row regseq ∨ hsame row realSeal)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
                        PkgSig bundle socketRead pkg ∧ PkgSig bundle realSeal pkg)
                    hsame ∧
                  UnaryHistory candidateRead ∧ UnaryHistory frontierRead ∧
                    UnaryHistory socketRead ∧ PkgSig bundle realSeal pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro ledger continuationLocalNameCandidate candidateHandoffFrontier
    frontierObstructionSocket frontierPkg socketPkg
  obtain ⟨packet, dyadicUnary, streamUnary, regseqUnary, realSealUnary,
    _dyadicStreamRegseq, _regseqRealSealHandoff, realSealPkg⟩ := ledger
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _unblockUnary,
    _dischargeUnary, handoffUnary, continuationUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormContinuation, _unblockObstructionDischarge,
    _handoffLocalName, _provenancePkg⟩ := packet
  have candidateUnary : UnaryHistory candidateRead :=
    unary_cont_closed continuationUnary localNameUnary continuationLocalNameCandidate
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed candidateUnary handoffUnary candidateHandoffFrontier
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed frontierUnary obstructionUnary frontierObstructionSocket
  have sourceFrontier :
      (fun row : BHist =>
        (hsame row frontierRead ∨ hsame row socketRead ∨ hsame row dyadic ∨
          hsame row stream ∨ hsame row regseq ∨ hsame row realSeal) ∧
          UnaryHistory row) frontierRead := by
    exact ⟨Or.inl (hsame_refl frontierRead), frontierUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row frontierRead ∨ hsame row socketRead ∨ hsame row dyadic ∨
              hsame row stream ∨ hsame row regseq ∨ hsame row realSeal) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row candidateRead ∨ hsame row frontierRead ∨ hsame row socketRead ∨
              hsame row dyadic ∨ hsame row stream ∨ hsame row regseq ∨
                hsame row realSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle frontierRead pkg ∧
              PkgSig bundle socketRead pkg ∧ PkgSig bundle realSeal pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead sourceFrontier
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
          ⟨by
            cases source.left with
            | inl sameFrontier =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier)
            | inr rest =>
                cases rest with
                | inl sameSocket =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameSocket))
                | inr rest =>
                    cases rest with
                    | inl sameDyadic =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameDyadic)))
                    | inr rest =>
                        cases rest with
                        | inl sameStream =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows) sameStream))))
                        | inr rest =>
                            cases rest with
                            | inl sameRegseq =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inl
                                            (hsame_trans
                                              (hsame_symm sameRows) sameRegseq)))))
                            | inr sameRealSeal =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (hsame_trans
                                              (hsame_symm sameRows) sameRealSeal)))))
            ,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameFrontier =>
          exact Or.inr (Or.inl sameFrontier)
      | inr rest =>
          cases rest with
          | inl sameSocket =>
              exact Or.inr (Or.inr (Or.inl sameSocket))
          | inr rest =>
              cases rest with
              | inl sameDyadic =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl sameDyadic)))
              | inr rest =>
                  cases rest with
                  | inl sameStream =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameStream))))
                  | inr rest =>
                      cases rest with
                      | inl sameRegseq =>
                          exact
                            Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRegseq)))))
                      | inr sameRealSeal =>
                          exact
                            Or.inr
                              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameRealSeal)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, frontierPkg, socketPkg, realSealPkg⟩
  }
  exact ⟨cert, candidateUnary, frontierUnary, socketUnary, realSealPkg⟩

theorem MetaCICCriticalPathKernelFrontierTotality [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName kernelRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont route localName kernelRead →
        Cont kernelRead obstruction frontierRead →
          PkgSig bundle frontierRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row kernelRead ∨ hsame row frontierRead ∨ hsame row obstruction ∨
                    hsame row dischargeSocket) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
                    hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                      hsame row kernelRead ∨ hsame row frontierRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont route localName kernelRead ∧
                    Cont kernelRead obstruction frontierRead ∧ PkgSig bundle frontierRead pkg ∧
                      PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory kernelRead ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet routeLocalNameKernel kernelObstructionFrontier frontierPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, _handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameKernel
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed kernelUnary obstructionUnary kernelObstructionFrontier
  have sourceKernel :
      (fun row : BHist =>
        (hsame row kernelRead ∨ hsame row frontierRead ∨ hsame row obstruction ∨
          hsame row dischargeSocket) ∧ UnaryHistory row) kernelRead := by
    exact ⟨Or.inl (hsame_refl kernelRead), kernelUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row kernelRead ∨ hsame row frontierRead ∨ hsame row obstruction ∨
              hsame row dischargeSocket) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row strongNorm ∨ hsame row normalForm ∨ hsame row obstruction ∨
              hsame row handoff ∨ hsame row dischargeSocket ∨ hsame row route ∨
                hsame row kernelRead ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont route localName kernelRead ∧
              Cont kernelRead obstruction frontierRead ∧ PkgSig bundle frontierRead pkg ∧
                PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro kernelRead sourceKernel
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
          ⟨by
            cases source.left with
            | inl sameKernel =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameKernel)
            | inr rest =>
                cases rest with
                | inl sameFrontier =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier))
                | inr rest =>
                    cases rest with
                    | inl sameObstruction =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inl
                                (hsame_trans (hsame_symm sameRows) sameObstruction)))
                    | inr sameSocket =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (hsame_trans (hsame_symm sameRows) sameSocket)))
            ,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameKernel =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr (Or.inl sameKernel))))))
      | inr rest =>
          cases rest with
          | inl sameFrontier =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr (Or.inr (Or.inr sameFrontier))))))
          | inr rest =>
              cases rest with
              | inl sameObstruction =>
                  exact Or.inr (Or.inr (Or.inl sameObstruction))
              | inr sameSocket =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSocket))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, routeLocalNameKernel, kernelObstructionFrontier, frontierPkg,
          provenancePkg⟩
  }
  exact ⟨cert, kernelUnary, frontierUnary⟩

theorem MetaCICCriticalPathDischargeSocketFrontierExhaustion [AskSetup] [PackageSetup]
    {strongNorm normalForm obstruction handoff dischargeSocket transport route provenance
      localName kernelRead socketRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICCriticalPathPacket strongNorm normalForm obstruction handoff dischargeSocket
        transport route provenance localName bundle pkg →
      Cont handoff obstruction socketRead →
        Cont route localName kernelRead →
          Cont kernelRead socketRead frontierRead →
            PkgSig bundle frontierRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    (hsame row socketRead ∨ hsame row frontierRead ∨
                      hsame row dischargeSocket) ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row handoff ∨ hsame row obstruction ∨
                      hsame row dischargeSocket ∨ hsame row socketRead ∨
                        hsame row kernelRead ∨ hsame row frontierRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont handoff obstruction socketRead ∧
                      Cont kernelRead socketRead frontierRead ∧
                        PkgSig bundle frontierRead pkg ∧ PkgSig bundle provenance pkg)
                  hsame ∧
                UnaryHistory socketRead ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle Pkg SemanticNameCert hsame
  intro packet handoffObstructionSocketRead routeLocalNameKernel kernelSocketFrontier
    frontierPkg
  obtain ⟨_strongNormUnary, _normalFormUnary, obstructionUnary, handoffUnary,
    dischargeSocketUnary, _transportUnary, routeUnary, _provenanceUnary, localNameUnary,
    _strongNormNormalFormRoute, _handoffObstructionSocket, _transportLocalName,
    provenancePkg⟩ := packet
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed handoffUnary obstructionUnary handoffObstructionSocketRead
  have kernelUnary : UnaryHistory kernelRead :=
    unary_cont_closed routeUnary localNameUnary routeLocalNameKernel
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed kernelUnary socketUnary kernelSocketFrontier
  have sourceSocket :
      (fun row : BHist =>
        (hsame row socketRead ∨ hsame row frontierRead ∨ hsame row dischargeSocket) ∧
          UnaryHistory row) socketRead := by
    exact ⟨Or.inl (hsame_refl socketRead), socketUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row socketRead ∨ hsame row frontierRead ∨ hsame row dischargeSocket) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row handoff ∨ hsame row obstruction ∨ hsame row dischargeSocket ∨
              hsame row socketRead ∨ hsame row kernelRead ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont handoff obstruction socketRead ∧
              Cont kernelRead socketRead frontierRead ∧ PkgSig bundle frontierRead pkg ∧
                PkgSig bundle provenance pkg)
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
          ⟨by
            cases source.left with
            | inl sameSocket =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameSocket)
            | inr rest =>
                cases rest with
                | inl sameFrontier =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFrontier))
                | inr sameDischargeSocket =>
                    exact
                      Or.inr
                        (Or.inr
                          (hsame_trans (hsame_symm sameRows) sameDischargeSocket))
            ,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSocket =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameSocket)))
      | inr rest =>
          cases rest with
          | inl sameFrontier =>
              exact
                Or.inr
                  (Or.inr (Or.inr (Or.inr (Or.inr sameFrontier))))
          | inr sameDischargeSocket =>
              exact Or.inr (Or.inr (Or.inl sameDischargeSocket))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, handoffObstructionSocketRead, kernelSocketFrontier, frontierPkg,
          provenancePkg⟩
  }
  exact ⟨cert, socketUnary, frontierUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
