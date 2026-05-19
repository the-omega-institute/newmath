import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_depth_ledger_coverage
    {Z S M R Q H C P N depthRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M Q depthRead ->
        Cont depthRead H ledgerRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory Q ∧
            UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory depthRead ∧
              UnaryHistory ledgerRead ∧ hsame H (append Z S) ∧ Cont M R Q ∧
                Cont M Q depthRead ∧ Cont depthRead H ledgerRead ∧ Cont Q H C ∧
                  Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet modulusDepthRead depthLedgerRead
  have carrierPacket := packet
  obtain ⟨unaryZ, unaryS, unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have closure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrierPacket
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM closure.left modulusDepthRead
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed depthUnary unaryH depthLedgerRead
  exact
    ⟨unaryZ, unaryS, unaryM, closure.left, unaryH, closure.right.left, depthUnary,
      ledgerUnary, closure.right.right.right, routeQ, modulusDepthRead, depthLedgerRead,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
