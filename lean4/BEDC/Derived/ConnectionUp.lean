import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ConnectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ConnectionCarrierPacket
    (base fibre sec tangent derivative provenance ledger : BHist) : Prop :=
  UnaryHistory base ∧ UnaryHistory fibre ∧ UnaryHistory tangent ∧ UnaryHistory provenance ∧
    Cont base fibre sec ∧ Cont sec tangent derivative ∧ Cont derivative provenance ledger

theorem ConnectionCarrierPacket_stability_ledger_exactness_obligation
    {base fibre sec tangent derivative provenance ledger : BHist} :
    ConnectionCarrierPacket base fibre sec tangent derivative provenance ledger ->
      UnaryHistory sec ∧ UnaryHistory derivative ∧ UnaryHistory ledger ∧
        hsame sec (append base fibre) ∧
          hsame derivative (append (append base fibre) tangent) ∧
            hsame ledger (append (append (append base fibre) tangent) provenance) := by
  intro packet
  have secUnary : UnaryHistory sec :=
    unary_cont_closed packet.left packet.right.left packet.right.right.right.right.left
  have derivativeUnary : UnaryHistory derivative :=
    unary_cont_closed secUnary packet.right.right.left packet.right.right.right.right.right.left
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed derivativeUnary packet.right.right.right.left
      packet.right.right.right.right.right.right
  have derivativeReadback : hsame derivative (append (append base fibre) tangent) :=
    hsame_trans packet.right.right.right.right.right.left
      (congrArg (fun h : BHist => append h tangent) packet.right.right.right.right.left)
  have ledgerReadback :
      hsame ledger (append (append (append base fibre) tangent) provenance) :=
    hsame_trans packet.right.right.right.right.right.right
      (congrArg (fun h : BHist => append h provenance) derivativeReadback)
  exact And.intro secUnary
    (And.intro derivativeUnary
      (And.intro ledgerUnary
        (And.intro packet.right.right.right.right.left
          (And.intro derivativeReadback ledgerReadback))))

end BEDC.Derived.ConnectionUp
