import BEDC.FKernel.Unary

namespace BEDC.Derived.ConnectionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

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
