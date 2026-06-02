import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem DecimalExpansionRegSeqRatDigitReplay
    {D W V Q R E H C P N prefixRead placeRead toleranceRead regseqRead sealRead
      replayRead namedRead : BHist} :
    UnaryHistory D ->
      UnaryHistory W ->
        UnaryHistory V ->
          UnaryHistory Q ->
            UnaryHistory R ->
              UnaryHistory E ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont D W prefixRead ->
                          Cont prefixRead V placeRead ->
                            Cont placeRead Q toleranceRead ->
                              Cont toleranceRead R regseqRead ->
                                Cont regseqRead E sealRead ->
                                  Cont sealRead C replayRead ->
                                    Cont replayRead N namedRead ->
                                      UnaryHistory prefixRead ∧ UnaryHistory placeRead ∧
                                        UnaryHistory toleranceRead ∧ UnaryHistory regseqRead ∧
                                          UnaryHistory sealRead ∧ UnaryHistory replayRead ∧
                                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary _hUnary cUnary _pUnary nUnary
    prefixRoute placeRoute toleranceRoute regseqRoute sealRoute replayRoute nameRoute
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary placeRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed placeUnary qUnary toleranceRoute
  have regseqUnary : UnaryHistory regseqRead :=
    unary_cont_closed toleranceUnary rUnary regseqRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regseqUnary eUnary sealRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed sealUnary cUnary replayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed replayUnary nUnary nameRoute
  exact
    ⟨prefixUnary, placeUnary, toleranceUnary, regseqUnary, sealUnary, replayUnary,
      namedUnary⟩

end BEDC.Derived.DecimalExpansionUp
