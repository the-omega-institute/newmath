import BEDC.Derived.CompactIntervalFixedPointUp.IntervalReturnRoute

namespace BEDC.Derived.CompactIntervalFixedPointUp.WindowRegularity

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPoint_window_regularity [AskSetup] [PackageSetup]
    {B W Q H C windowRead readbackRead replayRead transportedRead : BHist} :
    UnaryHistory B ->
      UnaryHistory W ->
        UnaryHistory Q ->
          UnaryHistory H ->
            UnaryHistory C ->
              Cont B W windowRead ->
                Cont windowRead Q readbackRead ->
                  Cont H C replayRead ->
                    hsame readbackRead transportedRead ->
                      hsame transportedRead (append (append B W) Q) ∧
                        UnaryHistory windowRead ∧
                          UnaryHistory transportedRead ∧
                            UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame append UnaryHistory
  intro bUnary wUnary qUnary hUnary cUnary windowRoute readbackRoute replayRoute
    readbackTransport
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_transport readbackUnary readbackTransport
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayRoute
  have readbackExact : hsame readbackRead (append (append B W) Q) :=
    readbackRoute.trans (congrArg (fun row => append row Q) windowRoute)
  have transportedExact : hsame transportedRead (append (append B W) Q) :=
    hsame_trans (hsame_symm readbackTransport) readbackExact
  exact ⟨transportedExact, windowUnary, transportedUnary, replayUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp.WindowRegularity
