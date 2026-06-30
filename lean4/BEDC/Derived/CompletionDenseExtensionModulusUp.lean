import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CompletionDenseExtensionModulusUp : Type where
  | mk
      (S U B W R D E H C P N : BHist) :
      CompletionDenseExtensionModulusUp
  deriving DecidableEq

end BEDC.Derived
