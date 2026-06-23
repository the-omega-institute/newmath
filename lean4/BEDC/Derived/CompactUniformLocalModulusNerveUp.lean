import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompactUniformLocalModulusNerveUp : Type where
  | mk
      (coverRows localModulusRows overlapRows lowerBoundRows triangleRows
        uniformModulusHandoff transport replay provenance name : BHist) :
      CompactUniformLocalModulusNerveUp
  deriving DecidableEq

end BEDC.Derived
