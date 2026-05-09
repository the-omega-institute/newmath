import BEDC.FKernel.Bundle
import BEDC.FKernel.Unary

namespace BEDC.Derived.FftUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def FftBHistSourcePacket
    (complex fourier stage schedule factor ledger endpoint : BHist)
    (bundle : ProbeBundle BHist) : Prop :=
  UnaryHistory complex ∧ UnaryHistory fourier ∧ UnaryHistory factor ∧ InBundle stage bundle ∧
    Cont complex fourier schedule ∧ Cont schedule factor ledger ∧ Cont ledger stage endpoint

theorem FftBHistSourcePacket_butterfly_schedule_obligation
    {complex fourier stage schedule factor ledger endpoint : BHist}
    {bundle : ProbeBundle BHist} :
    FftBHistSourcePacket complex fourier stage schedule factor ledger endpoint bundle ->
      InBundle stage bundle ∧ Cont complex fourier schedule ∧ Cont schedule factor ledger ∧
        Cont ledger stage endpoint ∧ UnaryHistory schedule ∧ UnaryHistory ledger := by
  intro packet
  have scheduleUnary : UnaryHistory schedule :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed scheduleUnary packet.right.right.left
      packet.right.right.right.right.right.left
  exact And.intro packet.right.right.right.left
    (And.intro packet.right.right.right.right.left
      (And.intro packet.right.right.right.right.right.left
        (And.intro packet.right.right.right.right.right.right
          (And.intro scheduleUnary ledgerUnary))))

end BEDC.Derived.FftUp
