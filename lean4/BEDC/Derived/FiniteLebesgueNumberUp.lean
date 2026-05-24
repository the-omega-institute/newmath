import BEDC.Derived.FiniteLebesgueNumberUp.Core
import BEDC.Derived.FiniteLebesgueNumberUp.BridgePacketExactness
import BEDC.Derived.FiniteLebesgueNumberUp.L10PhaseConsumerReadiness
import BEDC.Derived.FiniteLebesgueNumberUp.L10SiblingRoute
import BEDC.Derived.FiniteLebesgueNumberUp.CompactContinuousSourceAccountability
import BEDC.Derived.FiniteLebesgueNumberUp.CompactConsumerBoundaryRow
import BEDC.Derived.FiniteLebesgueNumberUp.CompactConsumerRadiusLedgerTotality
import BEDC.Derived.FiniteLebesgueNumberUp.CompactConsumerNonchoiceBoundary
import BEDC.Derived.FiniteLebesgueNumberUp.CompactMetricHandoffExactness
import BEDC.Derived.FiniteLebesgueNumberUp.PhaseRealRadiusWindowNoExtraSource
import BEDC.Derived.FiniteLebesgueNumberUp.RootRoutes
import BEDC.Derived.FiniteLebesgueNumberUp.PositiveRadiusCompactNetExport
import BEDC.Derived.FiniteLebesgueNumberUp.PublicCompactUniformExport
import BEDC.Derived.FiniteLebesgueNumberUp.DyadicCoverUniformModulusHandoff
import BEDC.Derived.FiniteLebesgueNumberUp.DyadicCoverCellSelection
import BEDC.Derived.FiniteLebesgueNumberUp.FiniteRadiusNonchoice
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusCover
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusCoverMonotoneReadback
import BEDC.Derived.FiniteLebesgueNumberUp.LedgerTransport
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusConsumerDeterminacy
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusMeshStabilityRow
import BEDC.Derived.FiniteLebesgueNumberUp.RadiusWindowAdmission
import BEDC.Derived.FiniteLebesgueNumberUp.OpenPhaseRadiusWindowExhaustion
import BEDC.Derived.FiniteLebesgueNumberUp.PhaseRealRadiusWindowSourceLock
import BEDC.Derived.FiniteLebesgueNumberUp.RootRadiusCoherencePackage
import BEDC.Derived.FiniteLebesgueNumberUp.RootTailRadiusSourcePackage
import BEDC.Derived.FiniteLebesgueNumberUp.OpenPhaseRootUnblockObligations
import BEDC.Derived.FiniteLebesgueNumberUp.OpenPhaseNonchoiceCover
import BEDC.Derived.FiniteLebesgueNumberUp.OpenPhaseSourceNonescape
import BEDC.Derived.FiniteLebesgueNumberUp.PhaseRealRadius
import BEDC.Derived.FiniteLebesgueNumberUp.RealPhaseSourceExhaustion
import BEDC.Derived.FiniteLebesgueNumberUp.RealSourceNonchoice
import BEDC.Derived.FiniteLebesgueNumberUp.RootCompactConsumerNonchoice
import BEDC.Derived.FiniteLebesgueNumberUp.RootUnblockTerminalPackage
import BEDC.Derived.FiniteLebesgueNumberUp.TerminalReadiness
import BEDC.Derived.FiniteLebesgueNumberUp.TerminalReadinessExitHandoff
import BEDC.Derived.FiniteLebesgueNumberUp.TotalBoundedConsumerFactorization
import BEDC.Derived.FiniteLebesgueNumberUp.SelectedTailBridgeLedger
import BEDC.Derived.FiniteLebesgueNumberUp.SelectedTailModulusExhaustion
import BEDC.Derived.FiniteLebesgueNumberUp.TailRadiusAdmission
import BEDC.Derived.FiniteLebesgueNumberUp.PhaseRealRadiusConsumerNonescape
import BEDC.Derived.FiniteLebesgueNumberUp.PhaseRealRadiusWindowExitConsumerReadiness
import BEDC.Derived.FiniteLebesgueNumberUp.PhaseRealRootUnblockPackage
import BEDC.Derived.FiniteLebesgueNumberUp.TerminalRadiusStability
import BEDC.Derived.FiniteLebesgueNumberUp.RootRadiusWindowConsumerExactness
import BEDC.Derived.FiniteLebesgueNumberUp.WindowRadiusLedgerCoherence
import BEDC.Derived.FiniteLebesgueNumberUp.WindowCoverageExactness
import BEDC.Derived.FiniteLebesgueNumberUp.SourceChainAdmission
import BEDC.Derived.FiniteLebesgueNumberUp.ObligationCoverageRow

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberChoiceFreeTailRadiusLedger_certificate [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow tailAdmission streamTail
      regularTail realTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh tailAdmission
        streamTail regularTail realTail transport route provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row realTail ∧
              FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh
                tailAdmission streamTail regularTail realTail transport route provenance
                nameRow bundle pkg)
          (fun row : BHist =>
            hsame row realTail ∧ Cont window radius tailAdmission ∧
              Cont tailAdmission mesh streamTail ∧ Cont streamTail route regularTail ∧
                Cont regularTail nameRow realTail)
          (fun row : BHist => hsame row realTail ∧ PkgSig bundle realTail pkg)
          hsame ∧
        UnaryHistory tailAdmission ∧ UnaryHistory streamTail ∧
          UnaryHistory regularTail ∧ UnaryHistory realTail ∧
            Cont window radius tailAdmission ∧ Cont tailAdmission mesh streamTail ∧
              Cont streamTail route regularTail ∧ Cont regularTail nameRow realTail ∧
                PkgSig bundle realTail pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh tailAdmission
        streamTail regularTail realTail transport route provenance nameRow bundle pkg :=
    ledger
  obtain ⟨carrier, windowRadiusTail, tailMeshStream, streamRouteRegular,
    regularNameReal, _provenancePkg, realPkg⟩ := ledger
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have tailUnary : UnaryHistory tailAdmission :=
    unary_cont_closed windowUnary radiusUnary windowRadiusTail
  have streamUnary : UnaryHistory streamTail :=
    unary_cont_closed tailUnary meshUnary tailMeshStream
  have regularUnary : UnaryHistory regularTail :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realTail :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  have sourceReal :
      (fun row : BHist =>
        hsame row realTail ∧
          FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh
            tailAdmission streamTail regularTail realTail transport route provenance
            nameRow bundle pkg) realTail := by
    exact ⟨hsame_refl realTail, ledgerPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row realTail ∧
              FiniteLebesgueNumberChoiceFreeTailRadiusLedger cover window radius mesh
                tailAdmission streamTail regularTail realTail transport route provenance
                nameRow bundle pkg)
          (fun row : BHist =>
            hsame row realTail ∧ Cont window radius tailAdmission ∧
              Cont tailAdmission mesh streamTail ∧ Cont streamTail route regularTail ∧
                Cont regularTail nameRow realTail)
          (fun row : BHist => hsame row realTail ∧ PkgSig bundle realTail pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro realTail sourceReal
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, windowRadiusTail, tailMeshStream, streamRouteRegular,
            regularNameReal⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, realPkg⟩
    }
  exact
    ⟨cert, tailUnary, streamUnary, regularUnary, realUnary, windowRadiusTail,
      tailMeshStream, streamRouteRegular, regularNameReal, realPkg⟩

def FiniteLebesgueNumberRealPhaseSourceExhaustionLedger [AskSetup] [PackageSetup]
    (cover radius mesh admission stream regular real transport replay provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FiniteLebesgueNumberCarrier cover admission radius mesh transport replay provenance
      nameRow bundle pkg ∧
    Cont cover radius admission ∧ Cont admission stream regular ∧
      Cont regular replay real ∧ PkgSig bundle real pkg

theorem FiniteLebesgueNumberRealPhaseSourceExhaustionLedger_certificate [AskSetup]
    [PackageSetup]
    {cover radius mesh admission stream regular real transport replay provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberRealPhaseSourceExhaustionLedger cover radius mesh admission
        stream regular real transport replay provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row real ∧
              FiniteLebesgueNumberRealPhaseSourceExhaustionLedger cover radius mesh
                admission stream regular real transport replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row real ∧ Cont cover radius admission ∧
              Cont admission stream regular ∧ Cont regular replay real)
          (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
          hsame ∧
        UnaryHistory cover ∧ UnaryHistory admission ∧ UnaryHistory radius ∧
          UnaryHistory mesh ∧ UnaryHistory replay ∧ Cont cover radius admission ∧
            Cont admission stream regular ∧ Cont regular replay real ∧
              PkgSig bundle real pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberRealPhaseSourceExhaustionLedger cover radius mesh admission
        stream regular real transport replay provenance nameRow bundle pkg :=
    ledger
  obtain ⟨carrier, coverRadiusAdmission, admissionStreamRegular, regularReplayReal,
    realPkg⟩ := ledger
  obtain ⟨coverUnary, admissionUnary, radiusUnary, meshUnary, _transportUnary,
    replayUnary, _provenanceUnary, _nameRowUnary, _coverAdmissionRadius,
    _radiusMeshReplay, _replayNameProvenance, _provenancePkg⟩ := carrier
  have admissionUnaryFromRoute : UnaryHistory admission :=
    unary_cont_closed coverUnary radiusUnary coverRadiusAdmission
  have sourceReal :
      (fun row : BHist =>
        hsame row real ∧
          FiniteLebesgueNumberRealPhaseSourceExhaustionLedger cover radius mesh
            admission stream regular real transport replay provenance nameRow bundle pkg)
          real := by
    exact ⟨hsame_refl real, ledgerPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row real ∧
              FiniteLebesgueNumberRealPhaseSourceExhaustionLedger cover radius mesh
                admission stream regular real transport replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row real ∧ Cont cover radius admission ∧
              Cont admission stream regular ∧ Cont regular replay real)
          (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro real sourceReal
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, coverRadiusAdmission, admissionStreamRegular, regularReplayReal⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, realPkg⟩
    }
  exact
    ⟨cert, coverUnary, admissionUnaryFromRoute, radiusUnary, meshUnary, replayUnary,
      coverRadiusAdmission, admissionStreamRegular, regularReplayReal, realPkg⟩

def FiniteLebesgueNumberRootRadiusCoherenceLedger [AskSetup] [PackageSetup]
    (cover radius mesh stream regular real transport replay provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FiniteLebesgueNumberCarrier cover stream radius mesh transport replay provenance
      nameRow bundle pkg ∧
    Cont cover radius stream ∧ Cont stream mesh regular ∧
      Cont regular replay real ∧ PkgSig bundle real pkg

theorem FiniteLebesgueNumberRootRadiusCoherenceLedger_certificate [AskSetup]
    [PackageSetup]
    {cover radius mesh stream regular real transport replay provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberRootRadiusCoherenceLedger cover radius mesh stream regular real
        transport replay provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row real ∧
              FiniteLebesgueNumberRootRadiusCoherenceLedger cover radius mesh stream regular
                real transport replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row real ∧ Cont cover radius stream ∧
              Cont stream mesh regular ∧ Cont regular replay real)
          (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
          hsame ∧
        UnaryHistory cover ∧ UnaryHistory stream ∧ UnaryHistory radius ∧
          UnaryHistory mesh ∧ UnaryHistory replay ∧ Cont cover radius stream ∧
            Cont stream mesh regular ∧ Cont regular replay real ∧
              PkgSig bundle real pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberRootRadiusCoherenceLedger cover radius mesh stream regular real
        transport replay provenance nameRow bundle pkg :=
    ledger
  obtain ⟨carrier, coverRadiusStream, streamMeshRegular, regularReplayReal, realPkg⟩ :=
    ledger
  obtain ⟨coverUnary, streamUnary, radiusUnary, meshUnary, _transportUnary, replayUnary,
    _provenanceUnary, _nameRowUnary, _coverStreamRadius, _radiusMeshReplay,
    _replayNameProvenance, _provenancePkg⟩ := carrier
  have streamUnaryFromRoute : UnaryHistory stream :=
    unary_cont_closed coverUnary radiusUnary coverRadiusStream
  have sourceReal :
      (fun row : BHist =>
        hsame row real ∧
          FiniteLebesgueNumberRootRadiusCoherenceLedger cover radius mesh stream regular
            real transport replay provenance nameRow bundle pkg) real := by
    exact ⟨hsame_refl real, ledgerPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row real ∧
              FiniteLebesgueNumberRootRadiusCoherenceLedger cover radius mesh stream regular
                real transport replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row real ∧ Cont cover radius stream ∧
              Cont stream mesh regular ∧ Cont regular replay real)
          (fun row : BHist => hsame row real ∧ PkgSig bundle real pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro real sourceReal
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, coverRadiusStream, streamMeshRegular, regularReplayReal⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, realPkg⟩
    }
  exact
    ⟨cert, coverUnary, streamUnaryFromRoute, radiusUnary, meshUnary, replayUnary,
      coverRadiusStream, streamMeshRegular, regularReplayReal, realPkg⟩

def FiniteLebesgueNumberCompactContinuousUnblockLedger [AskSetup] [PackageSetup]
    (cover window radius mesh transport route provenance nameRow compactRead continuousRead
      uniformRead : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
      bundle pkg ∧
    Cont radius mesh compactRead ∧ Cont compactRead route continuousRead ∧
      Cont continuousRead nameRow uniformRead ∧ PkgSig bundle uniformRead pkg

theorem FiniteLebesgueNumberCompactContinuousUnblockLedger_certificate [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow compactRead continuousRead
      uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh transport
        route provenance nameRow compactRead continuousRead uniformRead bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row uniformRead ∧
              FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh
                transport route provenance nameRow compactRead continuousRead uniformRead
                bundle pkg)
          (fun row : BHist =>
            hsame row uniformRead ∧ Cont radius mesh compactRead ∧
              Cont compactRead route continuousRead ∧
                Cont continuousRead nameRow uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame ∧
        UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
          UnaryHistory uniformRead ∧ Cont radius mesh compactRead ∧
            Cont compactRead route continuousRead ∧
              Cont continuousRead nameRow uniformRead ∧ PkgSig bundle uniformRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro ledger
  have ledgerPacket :
      FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh transport
        route provenance nameRow compactRead continuousRead uniformRead bundle pkg :=
    ledger
  obtain ⟨carrier, radiusMeshCompact, compactRouteContinuous, continuousNameUniform,
    uniformPkg⟩ := ledger
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have sourceUniform :
      (fun row : BHist =>
        hsame row uniformRead ∧
          FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh
            transport route provenance nameRow compactRead continuousRead uniformRead
            bundle pkg) uniformRead := by
    exact ⟨hsame_refl uniformRead, ledgerPacket⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row uniformRead ∧
              FiniteLebesgueNumberCompactContinuousUnblockLedger cover window radius mesh
                transport route provenance nameRow compactRead continuousRead uniformRead
                bundle pkg)
          (fun row : BHist =>
            hsame row uniformRead ∧ Cont radius mesh compactRead ∧
              Cont compactRead route continuousRead ∧
                Cont continuousRead nameRow uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, radiusMeshCompact, compactRouteContinuous,
            continuousNameUniform⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨cert, compactUnary, continuousUnary, uniformUnary, radiusMeshCompact,
      compactRouteContinuous, continuousNameUniform, uniformPkg⟩

theorem FiniteLebesgueNumberTerminalReadinessNoCompletenessPromotion [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow faceRead endpointRead
      completenessRead externalModulus : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont cover window faceRead →
        Cont faceRead radius endpointRead →
          PkgSig bundle endpointRead pkg →
            hsame completenessRead endpointRead →
              hsame externalModulus endpointRead →
                SemanticNameCert
                    (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                        hsame row route ∨ hsame row endpointRead)
                    (fun row : BHist =>
                      hsame row endpointRead ∧ PkgSig bundle endpointRead pkg)
                    hsame ∧
                  (∀ row : BHist,
                    (hsame row completenessRead ∨ hsame row externalModulus) →
                      hsame row endpointRead) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier coverWindowFace faceRadiusEndpoint endpointPkg sameCompleteness
    sameExternalModulus
  have handoff :
      SemanticNameCert
          (fun row : BHist => hsame row endpointRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cover ∨ hsame row window ∨ hsame row radius ∨
              hsame row route ∨ hsame row endpointRead)
          (fun row : BHist => hsame row endpointRead ∧ PkgSig bundle endpointRead pkg)
          hsame ∧
        UnaryHistory faceRead ∧ UnaryHistory endpointRead :=
    FiniteLebesgueNumberTerminalReadinessExitHandoff carrier coverWindowFace
      faceRadiusEndpoint endpointPkg
  refine ⟨handoff.left, ?_⟩
  intro row rowSource
  cases rowSource with
  | inl sameCompletenessRow =>
      exact hsame_trans sameCompletenessRow sameCompleteness
  | inr sameExternalRow =>
      exact hsame_trans sameExternalRow sameExternalModulus

theorem FiniteLebesgueNumberRealPhaseCoverageExport [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow dyadicRead streamRead
      regularRead realRead compactRead continuousRead uniformRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont radius mesh dyadicRead →
        Cont dyadicRead window streamRead →
          Cont streamRead route regularRead →
            Cont regularRead nameRow realRead →
              Cont realRead mesh compactRead →
                Cont compactRead route continuousRead →
                  Cont continuousRead nameRow uniformRead →
                    PkgSig bundle realRead pkg →
                      PkgSig bundle uniformRead pkg →
                        SemanticNameCert
                            (fun row : BHist =>
                              hsame row uniformRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row dyadicRead ∨ hsame row streamRead ∨
                                hsame row regularRead ∨ hsame row realRead ∨
                                  hsame row compactRead ∨ hsame row continuousRead ∨
                                    hsame row uniformRead)
                            (fun row : BHist =>
                              hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
                            hsame ∧
                          UnaryHistory dyadicRead ∧ UnaryHistory streamRead ∧
                            UnaryHistory regularRead ∧ UnaryHistory realRead ∧
                              UnaryHistory compactRead ∧ UnaryHistory continuousRead ∧
                                UnaryHistory uniformRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier radiusMeshDyadic dyadicWindowStream streamRouteRegular regularNameReal
    realMeshCompact compactRouteContinuous continuousNameUniform _realPkg uniformPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed radiusUnary meshUnary radiusMeshDyadic
  have streamUnary : UnaryHistory streamRead :=
    unary_cont_closed dyadicUnary windowUnary dyadicWindowStream
  have regularUnary : UnaryHistory regularRead :=
    unary_cont_closed streamUnary routeUnary streamRouteRegular
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed regularUnary nameRowUnary regularNameReal
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed realUnary meshUnary realMeshCompact
  have continuousUnary : UnaryHistory continuousRead :=
    unary_cont_closed compactUnary routeUnary compactRouteContinuous
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed continuousUnary nameRowUnary continuousNameUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row) uniformRead := by
    exact ⟨hsame_refl uniformRead, uniformUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row uniformRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row dyadicRead ∨ hsame row streamRead ∨
              hsame row regularRead ∨ hsame row realRead ∨
                hsame row compactRead ∨ hsame row continuousRead ∨
                  hsame row uniformRead)
          (fun row : BHist => hsame row uniformRead ∧ PkgSig bundle uniformRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformRead sourceUniform
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, uniformPkg⟩
    }
  exact
    ⟨cert, dyadicUnary, streamUnary, regularUnary, realUnary, compactUnary,
      continuousUnary, uniformUnary⟩

theorem FiniteLebesgueNumberRootWindowCoverTotality [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow windowRead coverCell
      realRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      Cont window radius windowRead ->
        Cont windowRead mesh coverCell ->
          Cont coverCell route realRead ->
            Cont realRead mesh compactRead ->
              PkgSig bundle compactRead pkg ->
                UnaryHistory windowRead ∧ UnaryHistory coverCell ∧
                  UnaryHistory realRead ∧ UnaryHistory compactRead ∧
                    Cont window radius windowRead ∧ Cont windowRead mesh coverCell ∧
                      Cont coverCell route realRead ∧ Cont realRead mesh compactRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle compactRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowRadiusRead readMeshCell cellRouteReal realMeshCompact compactPkg
  obtain ⟨_coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary radiusUnary windowRadiusRead
  have coverCellUnary : UnaryHistory coverCell :=
    unary_cont_closed windowReadUnary meshUnary readMeshCell
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed coverCellUnary routeUnary cellRouteReal
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed realReadUnary meshUnary realMeshCompact
  exact
    ⟨windowReadUnary, coverCellUnary, realReadUnary, compactReadUnary, windowRadiusRead,
      readMeshCell, cellRouteReal, realMeshCompact, provenancePkg, compactPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
