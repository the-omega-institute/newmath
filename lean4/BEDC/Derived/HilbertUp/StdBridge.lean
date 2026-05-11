import BEDC.Derived.HilbertUp

namespace BEDC.Derived.HilbertUp

open BEDC.Derived.RealUp
open BEDC.Derived.VecSpaceUp
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem HilbertUp_StdBridge :
    SemanticNameCert VecSpaceSingletonCarrier
        (fun h : BHist => VecSpaceSingletonClassifier (HilbertSingletonProjection h) BHist.Empty)
        (fun h : BHist =>
          RealConstantHistoryClassifier (HilbertSingletonInnerProduct h (HilbertSingletonProjection h))
            (BHist.e1 (BHist.e1 BHist.Empty)))
        VecSpaceSingletonClassifier ∧
      (∀ {m n : BHist}, VecSpaceSingletonCarrier m -> VecSpaceSingletonCarrier n ->
        RealConstantHistoryClassifier (HilbertSingletonInnerProduct m n)
          (BHist.e1 (BHist.e1 BHist.Empty))) := by
  constructor
  · exact HilbertSingletonProjection_semantic_name_certificate
  · intro m n carrierM carrierN
    exact HilbertSingleton_universal_orthogonality carrierM carrierN

end BEDC.Derived.HilbertUp
