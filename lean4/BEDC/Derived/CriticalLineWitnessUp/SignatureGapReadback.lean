import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def CriticalLineWitnessSignatureGapCarrier
    (Z S M R Q H C P N sig gap name : BHist) : Prop :=
  CriticalLineWitnessCarrier Z S M R Q H C P N ∧
    Cont Z S sig ∧ Cont M R gap ∧ Cont H C name ∧
      UnaryHistory sig ∧ UnaryHistory gap ∧ UnaryHistory name ∧ hsame H (append Z S)

end BEDC.Derived.CriticalLineWitnessUp
