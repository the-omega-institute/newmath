import BEDC.Derived.SeparableExtUp

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.Derived.FieldExtUp
open BEDC.Derived.SeparableExtUp

def GaloisExtSourcePacket
    (fieldExt polynomial normality separability classifier provenance ledger : BHist) : Prop :=
  FieldExtSingletonCarrier fieldExt ∧
    SeparableExtSourceRow fieldExt polynomial BHist.Empty fieldExt fieldExt separability
      provenance ∧
      Cont fieldExt separability classifier ∧
        Cont normality separability ledger

end BEDC.Derived.GaloisExtUp
