import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive IsometricCompletionUp : Type where
  | mk : (m k s f t u e r h c p n : BHist) → IsometricCompletionUp
  deriving DecidableEq

end BEDC.Derived
