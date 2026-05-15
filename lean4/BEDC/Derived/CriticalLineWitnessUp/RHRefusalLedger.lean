import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_refusal_ledger_completeness
    {Z S M R Q H C P N downstream : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q downstream ->
        UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
          UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory downstream ∧
            hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
              Cont N Q downstream := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet downstreamCont
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left downstreamCont
  exact
    ⟨packet.left, packet.right.left, packet.right.right.left, packet.right.right.right.left,
      routeClosure.left, routeClosure.right.left, routeClosure.right.right.left,
      downstreamUnary, routeClosure.right.right.right,
      packet.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.left,
      packet.right.right.right.right.right.right.right.right, downstreamCont⟩

end BEDC.Derived.CriticalLineWitnessUp
