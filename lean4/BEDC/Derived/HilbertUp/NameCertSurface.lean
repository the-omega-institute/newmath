import BEDC.Derived.HilbertUp

namespace BEDC.Derived.HilbertUp

open BEDC.Derived.NormUp
open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem HilbertSingletonOrthogonalProjection_namecert_surface :
    SemanticNameCert VecSpaceSingletonCarrier
      (fun h : BHist => VecSpaceSingletonClassifier (HilbertSingletonProjection h) BHist.Empty)
      (fun h : BHist =>
        RealConstantHistoryClassifier (HilbertSingletonInnerProduct h (HilbertSingletonProjection h))
          (BHist.e1 (BHist.e1 BHist.Empty)))
      VecSpaceSingletonClassifier ∧
      (∀ {h : BHist}, VecSpaceSingletonCarrier h →
        VecSpaceSingletonCarrier (HilbertSingletonProjection h) ∧
          VecSpaceSingletonClassifier h (HilbertSingletonProjection h) ∧
            RealConstantHistoryClassifier (NormSingletonNorm (HilbertSingletonProjection h))
              (BHist.e1 (BHist.e1 BHist.Empty)) ∧
              RealConstantHistoryClassifier
                (HilbertSingletonInnerProduct h (HilbertSingletonProjection h))
                (BHist.e1 (BHist.e1 BHist.Empty))) ∧
        (∀ {m p q : BHist}, HilbertSingletonProjectionWitness m p →
          HilbertSingletonProjectionWitness m q → VecSpaceSingletonClassifier p q) := by
  constructor
  · exact HilbertSingletonProjection_semantic_name_certificate
  · constructor
    · intro h carrierH
      have endpointRows := HilbertSingleton_projection_carried_endpoint carrierH
      have projectionEndpoint : VecSpaceSingletonClassifier (HilbertSingletonProjection h) BHist.Empty := by
        unfold HilbertSingletonProjection
        exact And.intro endpointRows.left
          (And.intro endpointRows.left (hsame_refl BHist.Empty))
      have projectionCarrier : VecSpaceSingletonCarrier (HilbertSingletonProjection h) :=
        projectionEndpoint.left
      have hProjection : VecSpaceSingletonClassifier h (HilbertSingletonProjection h) :=
        And.intro carrierH
          (And.intro projectionCarrier
            (hsame_trans carrierH (hsame_symm projectionEndpoint.left)))
      exact And.intro projectionCarrier
        (And.intro hProjection
          (And.intro endpointRows.right.right.right.left endpointRows.right.right.right.right))
    · intro m p q witnessP witnessQ
      exact (HilbertSingletonProjection_uniqueness witnessP witnessQ).left

end BEDC.Derived.HilbertUp
