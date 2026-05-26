import BEDC.FKernel.Ask
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package

namespace BEDC.Derived.SmythCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

def SmythCompletionCarrier [AskSetup] [PackageSetup]
    (U Q F R D M B I H C P N : BHist) : Prop :=
  Cont U Q (append U Q) ∧
    Cont Q F (append Q F) ∧
      Cont F R (append F R) ∧
        Cont R B (append R B) ∧
          Cont B I (append B I) ∧
            Cont I M (append I M) ∧
              Cont M D (append M D) ∧
                hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N

end BEDC.Derived.SmythCompletionUp
