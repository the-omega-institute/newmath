import BEDC.GroundCompiler.CaseStudies
import BEDC.GroundCompiler.MetricsFlow

namespace BEDC.GroundCompiler.CaseStudies

open BEDC.GroundCompiler.EventFlow
open BEDC.GroundCompiler.MetricsFlow
open BEDC.GroundCompiler.SemanticMotif
open BEDC.FKernel.Mark

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

end BEDC.GroundCompiler.CaseStudies
