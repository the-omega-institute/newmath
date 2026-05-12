import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def ModulusOfConvergenceCarrier
    (precision selector modulus schedule late ledger provenance : BHist) : Prop :=
  Cont precision selector modulus ∧ Cont schedule late ledger ∧ hsame provenance provenance

theorem ModulusOfConvergenceCarrier_tail_restriction_stability
    {p u mu s r l P tail l' : BHist}
    (packet : ModulusOfConvergenceCarrier p u mu s r l P)
    (tailRoute : Cont tail r l') :
    ModulusOfConvergenceCarrier p u mu tail r l' P := by
  cases packet with
  | intro precisionRoute rest =>
      cases rest with
      | intro _observationRoute sameProvenance =>
          constructor
          · exact precisionRoute
          · constructor
            · exact tailRoute
            · exact sameProvenance

end BEDC.Derived.ModulusOfConvergenceUp
