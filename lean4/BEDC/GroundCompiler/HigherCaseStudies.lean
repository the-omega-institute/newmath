import BEDC.GroundCompiler.CaseStudies
import BEDC.GroundCompiler.MetricsFlow

namespace BEDC.GroundCompiler.CaseStudies

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.MetricsFlow
open BEDC.GroundCompiler.SemanticMotif
open BEDC.FKernel.Mark

def RealApproximationSourceFlow : EventFlow :=
  [[BMark.b1, BMark.b1, BMark.b1, BMark.b0]]

def RealCauchyClassifierFlow : EventFlow :=
  [[BMark.b1, BMark.b1, BMark.b0, BMark.b1]]

def RealOperationDescentFlow : EventFlow :=
  [[BMark.b1, BMark.b0, BMark.b1, BMark.b1]]

def RealOrderCompatibilityFlow : EventFlow :=
  [[BMark.b0, BMark.b1, BMark.b0, BMark.b1]]

def RealMetricCompatibilityFlow : EventFlow :=
  [[BMark.b0, BMark.b0, BMark.b1, BMark.b1]]

def RealLedgerFlow : EventFlow :=
  [[BMark.b0, BMark.b0, BMark.b0, BMark.b1]]

def CompleteRealLikeFlow (S : EventFlow) : Prop :=
  CompletionMotif S /\
    Subflow RealApproximationSourceFlow S /\
    Subflow RealCauchyClassifierFlow S /\
    Subflow RealOperationDescentFlow S /\
    Subflow RealOrderCompatibilityFlow S /\
    Subflow RealMetricCompatibilityFlow S /\
    Subflow RealLedgerFlow S /\
    NonemptyEventFlow RealLedgerFlow

theorem completion_skeleton_motif :
    CompletionMotif CompletionSkeleton := by
  refine
    ⟨{ stage := FiniteRepetitionSkeleton 3,
        threadFlow := [[BMark.b0, BMark.b1]],
        classifier := [[BMark.b0, BMark.b1, BMark.b1]],
        sealFlow := [[BMark.b0, BMark.b1, BMark.b1]],
        ledgerFlow := [[BMark.b1, BMark.b0, BMark.b0]] }, ?_⟩
  constructor
  · exact prefix_subflow_subflow completion_skeleton_contains_repetition
  · constructor
    · exact Or.inl
        ⟨FiniteRepetitionSkeleton 3,
          [[BMark.b0, BMark.b1, BMark.b1],
            [BMark.b1, BMark.b0, BMark.b0]], rfl⟩
    · constructor
      · exact Or.inl
          ⟨List.append (FiniteRepetitionSkeleton 3) [[BMark.b0, BMark.b1]],
            [[BMark.b1, BMark.b0, BMark.b0]], rfl⟩
      · constructor
        · exact Or.inl
            ⟨List.append (FiniteRepetitionSkeleton 3) [[BMark.b0, BMark.b1]],
              [[BMark.b1, BMark.b0, BMark.b0]], rfl⟩
        · constructor
          · exact Or.inl
              ⟨List.append (FiniteRepetitionSkeleton 3)
                [[BMark.b0, BMark.b1], [BMark.b0, BMark.b1, BMark.b1]],
                [], rfl⟩
          · constructor
            · exact ⟨[BMark.b0, BMark.b1, BMark.b1], [], rfl⟩
            · exact ⟨[BMark.b1, BMark.b0, BMark.b0], [], rfl⟩

theorem real_approximation_not_in_completion_skeleton :
    Not (Subflow RealApproximationSourceFlow CompletionSkeleton) := by
  intro h
  have hMem :
      List.Mem [BMark.b1, BMark.b1, BMark.b1, BMark.b0]
        CompletionSkeleton :=
    subflow_mem h (List.Mem.head [])
  simp [CompletionSkeleton, FiniteRepetitionSkeleton, ZeroRunEvent] at hMem
  cases hMem with
  | tail _ hMem =>
      cases hMem with
      | tail _ hMem =>
          cases hMem with
          | tail _ hMem =>
              cases hMem with
              | tail _ hMem =>
                  cases hMem with
                  | tail _ hMem =>
                      cases hMem with
                      | tail _ hMem =>
                          cases hMem

theorem completion_necessary_not_sufficient_real :
    (forall {S : EventFlow}, CompleteRealLikeFlow S -> CompletionMotif S) /\
      exists S : EventFlow, CompletionMotif S /\ Not (CompleteRealLikeFlow S) := by
  constructor
  · intro S hReal
    exact hReal.left
  · refine ⟨CompletionSkeleton, completion_skeleton_motif, ?_⟩
    intro hReal
    exact real_approximation_not_in_completion_skeleton hReal.right.left

def TopologicalCompression (q : ClassifierCompressionData) : Nat × Nat :=
  CompressionRatio q

def TopologyMotifSkeleton : EventFlow :=
  [[BMark.b0, BMark.b0, BMark.b0, BMark.b0],
    [BMark.b0, BMark.b0, BMark.b0, BMark.b1],
    [BMark.b0, BMark.b0, BMark.b1, BMark.b0],
    [BMark.b0, BMark.b0, BMark.b1, BMark.b1],
    [BMark.b0, BMark.b1, BMark.b0, BMark.b0],
    [BMark.b0, BMark.b1, BMark.b0, BMark.b1]]

def ContinuityProofFlow : EventFlow :=
  [[BMark.b1, BMark.b1, BMark.b1, BMark.b1]]

def ContinuityProofMotif (S : EventFlow) : Prop :=
  Subflow ContinuityProofFlow S /\ NonemptyEventFlow ContinuityProofFlow

theorem topology_motif_skeleton_recognized :
    TopologyMotif TopologyMotifSkeleton := by
  constructor
  · exact Or.inr
        (IndexedSubflow.keep
          (IndexedSubflow.nil
          [[BMark.b0, BMark.b0, BMark.b0, BMark.b1],
            [BMark.b0, BMark.b0, BMark.b1, BMark.b0],
            [BMark.b0, BMark.b0, BMark.b1, BMark.b1],
            [BMark.b0, BMark.b1, BMark.b0, BMark.b0],
            [BMark.b0, BMark.b1, BMark.b0, BMark.b1]]))
  · constructor
    · exact Or.inr
        (IndexedSubflow.skip
          (IndexedSubflow.keep
            (IndexedSubflow.nil
              [[BMark.b0, BMark.b0, BMark.b1, BMark.b0],
                [BMark.b0, BMark.b0, BMark.b1, BMark.b1],
                [BMark.b0, BMark.b1, BMark.b0, BMark.b0],
                [BMark.b0, BMark.b1, BMark.b0, BMark.b1]])))
    · constructor
      · exact Or.inr
          (IndexedSubflow.skip
            (IndexedSubflow.skip
              (IndexedSubflow.keep
                (IndexedSubflow.nil
                  [[BMark.b0, BMark.b0, BMark.b1, BMark.b1],
                    [BMark.b0, BMark.b1, BMark.b0, BMark.b0],
                    [BMark.b0, BMark.b1, BMark.b0, BMark.b1]]))))
      · constructor
        · exact Or.inr
            (IndexedSubflow.skip
              (IndexedSubflow.skip
                (IndexedSubflow.skip
                  (IndexedSubflow.keep
                    (IndexedSubflow.nil
                      [[BMark.b0, BMark.b1, BMark.b0, BMark.b0],
                        [BMark.b0, BMark.b1, BMark.b0, BMark.b1]])))))
        · constructor
          · exact Or.inr
              (IndexedSubflow.skip
                (IndexedSubflow.skip
                  (IndexedSubflow.skip
                    (IndexedSubflow.skip
                      (IndexedSubflow.keep
                        (IndexedSubflow.nil
                          [[BMark.b0, BMark.b1, BMark.b0, BMark.b1]]))))))
          · constructor
            · exact Or.inr
                (IndexedSubflow.skip
                  (IndexedSubflow.skip
                    (IndexedSubflow.skip
                      (IndexedSubflow.skip
                        (IndexedSubflow.skip
                          (IndexedSubflow.keep
                            (IndexedSubflow.nil [])))))))
            · exact ⟨[BMark.b0, BMark.b1, BMark.b0, BMark.b0], [], rfl⟩

theorem topology_motif_not_continuity :
    exists S : EventFlow, TopologyMotif S /\ Not (ContinuityProofMotif S) := by
  refine ⟨TopologyMotifSkeleton, topology_motif_skeleton_recognized, ?_⟩
  intro hContinuity
  have hMem :
      List.Mem [BMark.b1, BMark.b1, BMark.b1, BMark.b1]
        TopologyMotifSkeleton :=
    subflow_mem hContinuity.left (List.Mem.head [])
  unfold TopologyMotifSkeleton at hMem
  cases hMem with
  | tail _ hMem =>
      cases hMem with
      | tail _ hMem =>
          cases hMem with
          | tail _ hMem =>
              cases hMem with
              | tail _ hMem =>
                  cases hMem with
                  | tail _ hMem =>
                      cases hMem with
                      | tail _ hMem =>
                          cases hMem

def CarryCandidateFlow : EventFlow :=
  [[BMark.b0, BMark.b1, BMark.b1], [BMark.b1, BMark.b0, BMark.b0]]

def CarryOnlyMotif (S : EventFlow) : Prop :=
  Subflow CarryCandidateFlow S /\ NonemptyEventFlow CarryCandidateFlow

def DimensionCertificateFlow : EventFlow :=
  [[BMark.b1, BMark.b1, BMark.b1, BMark.b1]]

def DimensionCertificateMotif (S : EventFlow) : Prop :=
  Subflow DimensionCertificateFlow S /\ NonemptyEventFlow DimensionCertificateFlow

theorem carry_motif_not_dimension :
    exists S : EventFlow, CarryOnlyMotif S /\ Not (DimensionCertificateMotif S) := by
  refine ⟨CarryCandidateFlow, ?_, ?_⟩
  · constructor
    · exact subflow_self CarryCandidateFlow
    · exact ⟨[BMark.b0, BMark.b1, BMark.b1],
        [[BMark.b1, BMark.b0, BMark.b0]], rfl⟩
  · intro hDimension
    have hMem :
        List.Mem [BMark.b1, BMark.b1, BMark.b1, BMark.b1]
          CarryCandidateFlow :=
      subflow_mem hDimension.left (List.Mem.head [])
    unfold CarryCandidateFlow at hMem
    cases hMem with
    | tail _ hMem =>
        cases hMem with
        | tail _ hMem =>
            cases hMem

def PhaseMotifSkeleton : EventFlow :=
  [[BMark.b0, BMark.b1, BMark.b1, BMark.b0],
    [BMark.b0, BMark.b1, BMark.b1, BMark.b1],
    [BMark.b1, BMark.b0, BMark.b0, BMark.b0],
    [BMark.b1, BMark.b0, BMark.b0, BMark.b1],
    [BMark.b1, BMark.b0, BMark.b1, BMark.b0]]

theorem phase_motif_skeleton_recognized :
    PhaseMotif PhaseMotifSkeleton := by
  constructor
  · exact Or.inl
      ⟨[],
        [[BMark.b0, BMark.b1, BMark.b1, BMark.b1],
          [BMark.b1, BMark.b0, BMark.b0, BMark.b0],
          [BMark.b1, BMark.b0, BMark.b0, BMark.b1],
          [BMark.b1, BMark.b0, BMark.b1, BMark.b0]], rfl⟩
  · constructor
    · exact Or.inl
        ⟨[[BMark.b0, BMark.b1, BMark.b1, BMark.b0]],
          [[BMark.b1, BMark.b0, BMark.b0, BMark.b0],
            [BMark.b1, BMark.b0, BMark.b0, BMark.b1],
            [BMark.b1, BMark.b0, BMark.b1, BMark.b0]], rfl⟩
    · constructor
      · exact Or.inl
          ⟨[[BMark.b0, BMark.b1, BMark.b1, BMark.b0],
            [BMark.b0, BMark.b1, BMark.b1, BMark.b1]],
            [[BMark.b1, BMark.b0, BMark.b0, BMark.b1],
              [BMark.b1, BMark.b0, BMark.b1, BMark.b0]], rfl⟩
      · constructor
        · exact Or.inl
            ⟨[[BMark.b0, BMark.b1, BMark.b1, BMark.b0],
              [BMark.b0, BMark.b1, BMark.b1, BMark.b1],
              [BMark.b1, BMark.b0, BMark.b0, BMark.b0]],
              [[BMark.b1, BMark.b0, BMark.b1, BMark.b0]], rfl⟩
        · constructor
          · exact Or.inl
              ⟨[[BMark.b0, BMark.b1, BMark.b1, BMark.b0],
                [BMark.b0, BMark.b1, BMark.b1, BMark.b1],
                [BMark.b1, BMark.b0, BMark.b0, BMark.b0],
                [BMark.b1, BMark.b0, BMark.b0, BMark.b1]], [], rfl⟩
          · exact ⟨[BMark.b1, BMark.b0, BMark.b1, BMark.b0], [], rfl⟩

theorem phase_motif_skeleton_not_circle :
    Not (CircleMotif PhaseMotifSkeleton) := by
  intro hCircle
  have hUnitMem :
      List.Mem [BMark.b0, BMark.b1, BMark.b0, BMark.b1]
        PhaseMotifSkeleton :=
    subflow_mem hCircle.right.left (List.Mem.head [])
  unfold PhaseMotifSkeleton at hUnitMem
  cases hUnitMem with
  | tail _ hUnitMem =>
      cases hUnitMem with
      | tail _ hUnitMem =>
          cases hUnitMem with
          | tail _ hUnitMem =>
              cases hUnitMem with
              | tail _ hUnitMem =>
                  cases hUnitMem with
                  | tail _ hUnitMem =>
                      cases hUnitMem

theorem phase_necessary_not_sufficient_circle :
    (forall {S : EventFlow}, CircleMotif S -> PhaseMotif S) /\
      exists S : EventFlow, PhaseMotif S /\ Not (CircleMotif S) := by
  constructor
  · intro S hCircle
    exact circle_extends_phase hCircle
  · exact
      ⟨PhaseMotifSkeleton, phase_motif_skeleton_recognized,
        phase_motif_skeleton_not_circle⟩

structure ComplexMotifRecord where
  productSource : EventFlow
  realComponentSource : EventFlow
  additionDescent : EventFlow
  multiplicationDescent : EventFlow
  rotationPhase : EventFlow
  conjugationNorm : EventFlow
  fieldClassifier : EventFlow
  ledger : EventFlow

def RecognizedComplexMotifRecord
    (S : EventFlow) (M : ComplexMotifRecord) : Prop :=
  Subflow M.productSource S /\
    Subflow M.realComponentSource S /\
    Subflow M.additionDescent S /\
    Subflow M.multiplicationDescent S /\
    Subflow M.rotationPhase S /\
    Subflow M.conjugationNorm S /\
    Subflow M.fieldClassifier S /\
    Subflow M.ledger S /\
    NonemptyEventFlow M.ledger

def ComplexMotif (S : EventFlow) : Prop :=
  exists M : ComplexMotifRecord, RecognizedComplexMotifRecord S M

structure ComplexAnalyticMotifRecord where
  complex : ComplexMotifRecord
  limitSource : EventFlow
  differenceQuotient : EventFlow
  analyticCompatibility : EventFlow
  localPowerSeries : EventFlow
  modulusLedger : EventFlow
  analyticSeal : EventFlow

def RecognizedComplexAnalyticMotifRecord
    (S : EventFlow) (M : ComplexAnalyticMotifRecord) : Prop :=
  RecognizedComplexMotifRecord S M.complex /\
    Subflow M.limitSource S /\
    Subflow M.differenceQuotient S /\
    Subflow M.analyticCompatibility S /\
    Subflow M.localPowerSeries S /\
    Subflow M.modulusLedger S /\
    Subflow M.analyticSeal S /\
    NonemptyEventFlow M.modulusLedger /\
    NonemptyEventFlow M.analyticSeal

def ComplexAnalyticMotif (S : EventFlow) : Prop :=
  exists M : ComplexAnalyticMotifRecord,
    RecognizedComplexAnalyticMotifRecord S M

theorem complex_analytic_extends_complex {S : EventFlow} :
    ComplexAnalyticMotif S -> ComplexMotif S := by
  intro h
  cases h with
  | intro M hM =>
      exact ⟨M.complex, hM.left⟩

structure ComplexReuseDepthRecord where
  realDepth : Nat
  productDepth : Nat
  complexDepth : Nat
  complexDepth_eq :
    complexDepth = Nat.succ (Nat.max realDepth productDepth)

theorem complex_reuse_depth (rec : ComplexReuseDepthRecord) :
    Nat.succ (Nat.max rec.realDepth rec.productDepth) <= rec.complexDepth := by
  rw [rec.complexDepth_eq]
  exact Nat.le_refl _

structure CategoryCompositionMotifRecord where
  objectSource : EventFlow
  morphismSource : EventFlow
  domainCodomainClassifier : EventFlow
  identityWitness : EventFlow
  compositionWitness : EventFlow
  associativityProof : EventFlow
  unitProof : EventFlow
  ledger : EventFlow

def RecognizedCategoryCompositionMotifRecord
    (S : EventFlow) (M : CategoryCompositionMotifRecord) : Prop :=
  Subflow M.objectSource S /\
    Subflow M.morphismSource S /\
    Subflow M.domainCodomainClassifier S /\
    Subflow M.identityWitness S /\
    Subflow M.compositionWitness S /\
    Subflow M.associativityProof S /\
    Subflow M.unitProof S /\
    Subflow M.ledger S /\
    NonemptyEventFlow M.ledger

def CategoryCompositionMotif (S : EventFlow) : Prop :=
  exists M : CategoryCompositionMotifRecord,
    RecognizedCategoryCompositionMotifRecord S M

structure FunctorMotifRecord where
  sourceCategory : CategoryCompositionMotifRecord
  targetCategory : CategoryCompositionMotifRecord
  objectMap : EventFlow
  morphismMap : EventFlow
  identityPreservation : EventFlow
  compositionPreservation : EventFlow
  ledger : EventFlow

def RecognizedFunctorMotifRecord
    (S : EventFlow) (M : FunctorMotifRecord) : Prop :=
  RecognizedCategoryCompositionMotifRecord S M.sourceCategory /\
    RecognizedCategoryCompositionMotifRecord S M.targetCategory /\
    Subflow M.objectMap S /\
    Subflow M.morphismMap S /\
    Subflow M.identityPreservation S /\
    Subflow M.compositionPreservation S /\
    Subflow M.ledger S /\
    NonemptyEventFlow M.ledger

def FunctorMotif (S : EventFlow) : Prop :=
  exists M : FunctorMotifRecord, RecognizedFunctorMotifRecord S M

theorem functor_extends_category {S : EventFlow} :
    FunctorMotif S ->
      exists C D : CategoryCompositionMotifRecord,
        RecognizedCategoryCompositionMotifRecord S C /\
          RecognizedCategoryCompositionMotifRecord S D := by
  intro h
  cases h with
  | intro M hM =>
      exact ⟨M.sourceCategory, M.targetCategory, hM.left, hM.right.left⟩

structure NaturalTransformationMotifRecord where
  sourceFunctor : FunctorMotifRecord
  targetFunctor : FunctorMotifRecord
  componentFamily : EventFlow
  naturalitySquareProof : EventFlow
  componentLedger : EventFlow

def RecognizedNaturalTransformationMotifRecord
    (S : EventFlow) (M : NaturalTransformationMotifRecord) : Prop :=
  RecognizedFunctorMotifRecord S M.sourceFunctor /\
    RecognizedFunctorMotifRecord S M.targetFunctor /\
    Subflow M.componentFamily S /\
    Subflow M.naturalitySquareProof S /\
    Subflow M.componentLedger S /\
    NonemptyEventFlow M.componentLedger

def NaturalTransformationMotif (S : EventFlow) : Prop :=
  exists M : NaturalTransformationMotifRecord,
    RecognizedNaturalTransformationMotifRecord S M

theorem natural_transformation_extends_functor {S : EventFlow} :
    NaturalTransformationMotif S ->
      exists F G : FunctorMotifRecord,
        RecognizedFunctorMotifRecord S F /\
          RecognizedFunctorMotifRecord S G := by
  intro h
  cases h with
  | intro M hM =>
      exact ⟨M.sourceFunctor, M.targetFunctor, hM.left, hM.right.left⟩

structure ChainComplexMotifRecord where
  gradedObject : EventFlow
  boundaryMap : EventFlow
  boundaryComposition : EventFlow
  zeroCompositionProof : EventFlow
  chainLedger : EventFlow

def RecognizedChainComplexMotifRecord
    (S : EventFlow) (M : ChainComplexMotifRecord) : Prop :=
  Subflow M.gradedObject S /\
    Subflow M.boundaryMap S /\
    Subflow M.boundaryComposition S /\
    Subflow M.zeroCompositionProof S /\
    Subflow M.chainLedger S /\
    NonemptyEventFlow M.chainLedger

def ChainComplexMotif (S : EventFlow) : Prop :=
  exists M : ChainComplexMotifRecord,
    RecognizedChainComplexMotifRecord S M

structure CycleBoundaryClassifierMotifRecord where
  cycleFlow : EventFlow
  boundaryFlow : EventFlow
  boundaryEquivalence : EventFlow
  quotientClassifier : EventFlow
  exactnessLedger : EventFlow

def RecognizedCycleBoundaryClassifierMotifRecord
    (S : EventFlow) (M : CycleBoundaryClassifierMotifRecord) : Prop :=
  Subflow M.cycleFlow S /\
    Subflow M.boundaryFlow S /\
    Subflow M.boundaryEquivalence S /\
    Subflow M.quotientClassifier S /\
    Subflow M.exactnessLedger S /\
    NonemptyEventFlow M.boundaryEquivalence /\
    NonemptyEventFlow M.quotientClassifier /\
    NonemptyEventFlow M.exactnessLedger

def CycleBoundaryClassifierMotif (S : EventFlow) : Prop :=
  exists M : CycleBoundaryClassifierMotifRecord,
    RecognizedCycleBoundaryClassifierMotifRecord S M

structure HomologyMotifRecord where
  chainComplex : ChainComplexMotifRecord
  cycleBoundaryClassifier : CycleBoundaryClassifierMotifRecord
  quotientFlow : EventFlow
  exactnessProof : EventFlow
  homologyLedger : EventFlow

def RecognizedHomologyMotifRecord
    (S : EventFlow) (M : HomologyMotifRecord) : Prop :=
  RecognizedChainComplexMotifRecord S M.chainComplex /\
    RecognizedCycleBoundaryClassifierMotifRecord S M.cycleBoundaryClassifier /\
    Subflow M.quotientFlow S /\
    Subflow M.exactnessProof S /\
    Subflow M.homologyLedger S /\
    NonemptyEventFlow M.homologyLedger

def HomologyMotif (S : EventFlow) : Prop :=
  exists M : HomologyMotifRecord, RecognizedHomologyMotifRecord S M

theorem homology_has_classifier_compression {S : EventFlow} :
    HomologyMotif S -> CycleBoundaryClassifierMotif S := by
  intro h
  cases h with
  | intro M hM =>
      exact ⟨M.cycleBoundaryClassifier, hM.right.left⟩

structure CrossDomainMotifComparison where
  recognizers : MetricRecognizerFamily
  protocol : AnalysisProtocolFlow
  leftFlow : EventFlow
  rightFlow : EventFlow
  leftProfile : List BEDC.GroundCompiler.MetricsFlow.MotifOccurrence
  rightProfile : List BEDC.GroundCompiler.MetricsFlow.MotifOccurrence
  overlap : Nat × Nat
  overlap_eq : overlap = MotifJaccardDistance leftProfile rightProfile
  theoryComponents : TheoryDistanceComponents
  theoryDistance : Nat
  theoryDistance_eq :
    theoryDistance =
      TheoryFlowDistance recognizers protocol leftFlow rightFlow theoryComponents

def CrossDomainSharedMotifFlow : EventFlow :=
  [[BMark.b0, BMark.b1, BMark.b0, BMark.b1, BMark.b0]]

def CrossDomainOverlapLeftFlow : EventFlow :=
  CrossDomainSharedMotifFlow

def CrossDomainOverlapRightFlow : EventFlow :=
  CrossDomainSharedMotifFlow

def CrossDomainMotifOverlapFlow (S T : EventFlow) : Prop :=
  Subflow CrossDomainSharedMotifFlow S /\
    Subflow CrossDomainSharedMotifFlow T /\
    NonemptyEventFlow CrossDomainSharedMotifFlow

def BridgeMotifFlow : EventFlow :=
  [[BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]]

def BridgeTranslationSupportFlow : EventFlow :=
  [[BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1]]

def BridgeSoundnessSupportFlow : EventFlow :=
  [[BMark.b1, BMark.b1, BMark.b1, BMark.b0, BMark.b1]]

def BridgeLedgerSupportFlow : EventFlow :=
  [[BMark.b1, BMark.b1, BMark.b0, BMark.b1, BMark.b1]]

def BridgeCertificateSupport (S T : EventFlow) : Prop :=
  Subflow BridgeTranslationSupportFlow S /\
    Subflow BridgeSoundnessSupportFlow T /\
    Subflow BridgeLedgerSupportFlow S /\
    NonemptyEventFlow BridgeLedgerSupportFlow

def RecognizedBridgeFlow (S T : EventFlow) : Prop :=
  CrossDomainMotifOverlapFlow S T /\
    Subflow BridgeMotifFlow S /\
    Subflow BridgeMotifFlow T /\
    BridgeCertificateSupport S T

theorem cross_domain_overlap_witness :
    CrossDomainMotifOverlapFlow
      CrossDomainOverlapLeftFlow CrossDomainOverlapRightFlow := by
  constructor
  · exact subflow_self CrossDomainSharedMotifFlow
  · constructor
    · exact subflow_self CrossDomainSharedMotifFlow
    · exact ⟨[BMark.b0, BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        [], rfl⟩

theorem bridge_motif_not_in_overlap_left :
    Not (Subflow BridgeMotifFlow CrossDomainOverlapLeftFlow) := by
  intro h
  have hBridgeHead :
      List.Mem [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]
        BridgeMotifFlow := by
    unfold BridgeMotifFlow
    exact List.Mem.head []
  have hMem :
      List.Mem [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0]
        CrossDomainOverlapLeftFlow :=
    subflow_mem h hBridgeHead
  unfold CrossDomainOverlapLeftFlow CrossDomainSharedMotifFlow at hMem
  cases hMem with
  | tail _ htail => cases htail

theorem overlap_not_bridge :
    exists S T : EventFlow,
      CrossDomainMotifOverlapFlow S T /\ Not (RecognizedBridgeFlow S T) := by
  refine
    ⟨CrossDomainOverlapLeftFlow, CrossDomainOverlapRightFlow,
      cross_domain_overlap_witness, ?_⟩
  intro hBridge
  exact bridge_motif_not_in_overlap_left hBridge.right.left

theorem bridge_needs_cert {S T : EventFlow} :
    RecognizedBridgeFlow S T ->
      (Subflow BridgeMotifFlow S /\ Subflow BridgeMotifFlow T) /\
        BridgeCertificateSupport S T := by
  intro h
  exact ⟨⟨h.right.left, h.right.right.left⟩, h.right.right.right⟩

structure HighLevelMotifReport where
  sourceFlow : EventFlow
  motifBundle : List HighLayerMotifRole
  signature : FlowSignatureVector
  normalAddressMap : List NormalAddressRecord
  warnings : List EventFlow
  cannotClaims : List MetricCannotClaimEntry
  cannotClaims_present : exists entry : MetricCannotClaimEntry,
    List.Mem entry cannotClaims

theorem high_level_reports_require_cannot_claims
    (report : HighLevelMotifReport) :
    exists entry : MetricCannotClaimEntry, List.Mem entry report.cannotClaims :=
  report.cannotClaims_present

theorem high_layer_motifs_cannot_replace_certificates :
    Not (forall Rfam : GeneratedMotifRecognizer -> Prop,
      forall S : EventFlow,
      forall role : HighLayerMotifRole,
      forall M L : EventFlow,
        HighLayerMotif Rfam S role M L -> AcceptedObjectFlow S) := by
  intro h
  let role : HighLayerMotifRole := HighLayerMotifRole.completion
  have hRecognizes : RecognizesMotif [] [] [] role.code :=
    ⟨FormalCompilerInput.eventFlow [],
      ⟨FormalCompilerInput.eventFlow [],
        FormalCompilerInput.eventFlow [],
        FormalCompilerInput.eventFlow role.code⟩,
      Or.inl ⟨[], [], rfl⟩⟩
  have hMotif : HighLayerMotif EmptyRfam [] role [] [] :=
    ⟨[], rfl, hRecognizes, hRecognizes, Or.inl ⟨[], [], rfl⟩⟩
  exact empty_not_accepted_object_flow (h EmptyRfam [] role [] [] hMotif)

theorem higher_layer_conservativity
    {Rfam : GeneratedMotifRecognizer -> Prop} {S : EventFlow}
    {role : HighLayerMotifRole} {M L : EventFlow} :
    HighLayerMotif Rfam S role M L -> CaseStudyFlowUsesOnlyDisplayAlphabet S := by
  intro _ w _ m _
  cases m with
  | b0 => exact Or.inl rfl
  | b1 => exact Or.inr rfl

end BEDC.GroundCompiler.CaseStudies
