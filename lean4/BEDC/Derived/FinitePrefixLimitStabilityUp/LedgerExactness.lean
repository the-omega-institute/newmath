import BEDC.Derived.FinitePrefixLimitStabilityUp.TasteGate

namespace BEDC.Derived.FinitePrefixLimitStabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem FinitePrefixLimitStabilityLedgerExactness
    {B W R D E H C P N BW WR RD DE ledger : BHist}
    (hB : UnaryHistory B) (hW : UnaryHistory W) (hR : UnaryHistory R)
    (hD : UnaryHistory D) (hE : UnaryHistory E) (hH : UnaryHistory H)
    (hC : UnaryHistory C) (hBW : Cont B W BW) (hWR : Cont BW R WR)
    (hRD : Cont WR D RD) (hDE : Cont RD E DE) (hLedger : Cont H C ledger) :
    FieldFaithful.fields (FinitePrefixLimitStabilityUp.packet B W R D E H C P N) =
        [B, W, R, D, E, H, C, P, N] ∧
      UnaryHistory BW ∧ UnaryHistory WR ∧ UnaryHistory RD ∧ UnaryHistory DE ∧
        UnaryHistory ledger ∧ Cont H C ledger := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory FieldFaithful
  have route :=
    @FinitePrefixLimitStabilityCarrier_route_unary_closure
      B W R D E H C P N BW WR RD DE hB hW hR hD hE hBW hWR hRD hDE
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed hH hC hLedger
  exact
    ⟨route.1, route.2.1, route.2.2.1, route.2.2.2.1, route.2.2.2.2,
      ledgerUnary, hLedger⟩

end BEDC.Derived.FinitePrefixLimitStabilityUp
