import BEDC.Derived.DiffFormUp

namespace BEDC.Derived.DiffFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def DiffFormExteriorDerivativeVisibleInputPackage
    (omega domega degree degreePlus probe probePlus tensor tensorPlus scalar scalarPlus
      source : BHist) :
    Prop :=
  DiffFormExteriorDerivativeLedger omega domega degree degreePlus probe probePlus tensor
      tensorPlus scalar scalarPlus (append probe tensor) source ∧
    Cont degree (BHist.e1 BHist.Empty) degreePlus ∧ hsame source (append omega domega)

end BEDC.Derived.DiffFormUp
