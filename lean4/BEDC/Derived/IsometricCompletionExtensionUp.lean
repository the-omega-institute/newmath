import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive IsometricCompletionExtensionUp : Type where
  | mk : (m d k g r h c p n : BHist) → IsometricCompletionExtensionUp
  deriving DecidableEq

end BEDC.Derived
