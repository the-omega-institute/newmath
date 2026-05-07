import BEDC.Derived.SheafUp

namespace BEDC.Derived.SheafUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def SheafDownstreamRootSource
    (root carrier classifier restriction cover baseChange refinement exactness : BHist) : Prop :=
  UnaryHistory root ∧
    SheafBHistPointGermLedger root carrier restriction exactness ∧
      SheafBHistCoverNerveLedger root cover baseChange refinement exactness ∧
        hsame carrier classifier

end BEDC.Derived.SheafUp
