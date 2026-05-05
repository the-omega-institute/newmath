import BEDC.FKernel.Cont
import BEDC.Derived.FieldUp
import BEDC.Derived.VecSpaceUp

namespace BEDC.Derived.FieldExtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.FieldUp
open BEDC.Derived.VecSpaceUp

def FieldExtSingletonEmbedding (h : BHist) : BHist :=
  append BHist.Empty h

theorem FieldExtSingletonVectorSpace_smul_mul_compatible {r m : BHist} :
    FieldSingletonCarrier r -> VecSpaceSingletonCarrier m ->
      VecSpaceSingletonCarrier (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m) ∧
        FieldSingletonCarrier (FieldSingletonMul (FieldExtSingletonEmbedding r) m) ∧
          hsame (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m)
            (FieldSingletonMul (FieldExtSingletonEmbedding r) m) := by
  intro _carrierR _carrierM
  have smulCarrier :
      VecSpaceSingletonCarrier (VecSpaceSingletonSmul (FieldExtSingletonEmbedding r) m) :=
    hsame_refl BHist.Empty
  have mulCarrier :
      FieldSingletonCarrier (FieldSingletonMul (FieldExtSingletonEmbedding r) m) :=
    hsame_refl BHist.Empty
  exact And.intro smulCarrier
    (And.intro mulCarrier (hsame_refl BHist.Empty))

end BEDC.Derived.FieldExtUp
