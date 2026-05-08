import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary
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

theorem ConnectionCarrierPacket_curvature_boundary_obligation
    {base fibre sec tangentA tangentB derivativeA derivativeB provenance ledgerA ledgerB
      boundary curvatureLedger : BHist} :
    ConnectionCarrierPacket base fibre sec tangentA derivativeA provenance ledgerA ->
      ConnectionCarrierPacket base fibre sec tangentB derivativeB provenance ledgerB ->
        Cont derivativeA derivativeB boundary ->
          Cont boundary provenance curvatureLedger ->
            UnaryHistory boundary ∧ UnaryHistory curvatureLedger ∧
              hsame boundary (append derivativeA derivativeB) ∧
                hsame curvatureLedger (append boundary provenance) ∧
                  hsame curvatureLedger
                    (append (append (append base fibre) tangentA)
                      (append (append (append base fibre) tangentB) provenance)) := by
  intro packetA packetB boundaryLedger curvatureLedgerRead
  have exactA :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetA
  have exactB :=
    ConnectionCarrierPacket_stability_ledger_exactness_obligation packetB
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed exactA.right.left exactB.right.left boundaryLedger
  have curvatureUnary : UnaryHistory curvatureLedger :=
    unary_cont_closed boundaryUnary packetA.right.right.right.left curvatureLedgerRead
  have boundaryReadback : hsame boundary (append derivativeA derivativeB) :=
    boundaryLedger
  have curvatureReadback : hsame curvatureLedger (append boundary provenance) :=
    curvatureLedgerRead
  have curvatureWithDerivatives :
      hsame curvatureLedger (append derivativeA (append derivativeB provenance)) :=
    hsame_trans
      (hsame_trans curvatureReadback
        (congrArg (fun h : BHist => append h provenance) boundaryReadback))
      (append_assoc derivativeA derivativeB provenance)
  have curvatureWithFirstTangent :
      hsame curvatureLedger
        (append (append (append base fibre) tangentA) (append derivativeB provenance)) :=
    hsame_trans curvatureWithDerivatives
      (congrArg (fun h : BHist => append h (append derivativeB provenance))
        exactA.right.right.right.right.left)
  have curvatureWithTangents :
      hsame curvatureLedger
        (append (append (append base fibre) tangentA)
          (append (append (append base fibre) tangentB) provenance)) :=
    hsame_trans curvatureWithFirstTangent
      (congrArg
        (fun h : BHist => append (append (append base fibre) tangentA) (append h provenance))
        exactB.right.right.right.right.left)
  exact And.intro boundaryUnary
    (And.intro curvatureUnary
      (And.intro boundaryReadback
        (And.intro curvatureReadback curvatureWithTangents)))

def ConnectionTransportSteps : List BHist → Prop
  | [] => hsame BHist.Empty BHist.Empty
  | step :: rest => UnaryHistory step ∧ ConnectionTransportSteps rest

def ConnectionParallelTransportSpine : List BHist → BHist → BHist → Prop
  | [], initial, terminal => hsame initial terminal
  | step :: rest, initial, terminal =>
      ∃ middle : BHist,
        Cont initial step middle ∧ ConnectionParallelTransportSpine rest middle terminal

theorem ConnectionCarrierPacket_parallel_transport_obligation
    {steps : List BHist} {initial terminal : BHist} :
    UnaryHistory initial → ConnectionTransportSteps steps →
      ConnectionParallelTransportSpine steps initial terminal → UnaryHistory terminal := by
  intro unaryInitial stepRows spine
  induction steps generalizing initial with
  | nil =>
      exact unary_transport unaryInitial spine
  | cons step rest ih =>
      cases stepRows with
      | intro stepUnary restRows =>
          cases spine with
          | intro middle tail =>
              exact ih (unary_cont_closed unaryInitial stepUnary tail.left) restRows tail.right

end BEDC.Derived.ConnectionUp
