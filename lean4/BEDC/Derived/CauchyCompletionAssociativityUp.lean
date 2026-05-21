import BEDC.FKernel.Hist

namespace BEDC.Derived

open BEDC.FKernel.Hist

inductive CauchyCompletionAssociativityUp : Type where
  | mk
      (monad unit counit idempotence minimality stream regular dyadic real leftRoute
        rightRoute transport replay provenance localName : BHist) :
      CauchyCompletionAssociativityUp
  deriving DecidableEq

end BEDC.Derived
