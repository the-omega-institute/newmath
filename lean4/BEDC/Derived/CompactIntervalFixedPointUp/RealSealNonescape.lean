import BEDC.Derived.CompactIntervalFixedPointUp.WindowRegularity

namespace BEDC.Derived.CompactIntervalFixedPointUp.RealSealNonescape

open BEDC.FKernel.Ask
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPoint_real_seal_nonescape [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N mapRead returnRead bisectionRead windowRead readbackRead
      sealRead replayRead : BHist} :
    UnaryHistory J →
      UnaryHistory G →
        UnaryHistory R →
          UnaryHistory B →
            UnaryHistory W →
              UnaryHistory Q →
                UnaryHistory E →
                  UnaryHistory H →
                    UnaryHistory C →
                      Cont J G mapRead →
                        Cont mapRead R returnRead →
                          Cont returnRead B bisectionRead →
                            Cont bisectionRead W windowRead →
                              Cont windowRead Q readbackRead →
                                Cont readbackRead E sealRead →
                                  Cont H C replayRead →
                                    hsame sealRead
                                        (append (append (append (append (append (append J G) R) B) W) Q) E) ∧
                                      UnaryHistory sealRead ∧ UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont append hsame UnaryHistory
  intro jUnary gUnary rUnary bUnary wUnary qUnary eUnary hUnary cUnary mapCont
    returnCont bisectionCont windowCont readbackCont sealCont replayCont
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed jUnary gUnary mapCont
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed mapUnary rUnary returnCont
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed returnUnary bUnary bisectionCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bisectionUnary wUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealCont
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayCont
  have mapExact : hsame mapRead (append J G) :=
    mapCont
  have returnExact : hsame returnRead (append (append J G) R) :=
    returnCont.trans (congrArg (fun row => append row R) mapExact)
  have bisectionExact : hsame bisectionRead (append (append (append J G) R) B) :=
    bisectionCont.trans (congrArg (fun row => append row B) returnExact)
  have windowExact : hsame windowRead (append (append (append (append J G) R) B) W) :=
    windowCont.trans (congrArg (fun row => append row W) bisectionExact)
  have readbackExact : hsame readbackRead
      (append (append (append (append (append J G) R) B) W) Q) :=
    readbackCont.trans (congrArg (fun row => append row Q) windowExact)
  have sealExact : hsame sealRead
      (append (append (append (append (append (append J G) R) B) W) Q) E) :=
    sealCont.trans (congrArg (fun row => append row E) readbackExact)
  exact ⟨sealExact, sealUnary, replayUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp.RealSealNonescape
