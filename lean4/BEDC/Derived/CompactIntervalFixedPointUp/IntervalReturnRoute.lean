import BEDC.Derived.CompactIntervalFixedPointUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CompactIntervalFixedPointUp.IntervalReturnRoute

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPoint_interval_return_route [AskSetup] [PackageSetup]
    {J G R B W Q E H C P N mapRead returnRead bisectionRead windowRead readbackRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory J →
      UnaryHistory G →
        UnaryHistory R →
          UnaryHistory B →
            UnaryHistory W →
              UnaryHistory Q →
                UnaryHistory E →
                  UnaryHistory P →
                    UnaryHistory N →
                      PkgSig bundle P pkg →
                        Cont J G mapRead →
                          Cont mapRead R returnRead →
                            Cont returnRead B bisectionRead →
                              Cont bisectionRead W windowRead →
                                Cont windowRead Q readbackRead →
                                  Cont readbackRead E sealRead →
                                    hsame sealRead
                                        (append (append (append (append (append (append J G) R) B) W) Q) E) ∧
                                      UnaryHistory mapRead ∧ UnaryHistory returnRead ∧
                                        UnaryHistory bisectionRead ∧ UnaryHistory windowRead ∧
                                          UnaryHistory readbackRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame append ProbeBundle PkgSig UnaryHistory
  intro jUnary gUnary rUnary bUnary wUnary qUnary eUnary _pUnary _nUnary _pkg
    mapRoute returnRoute bisectionRoute windowRoute readbackRoute sealRoute
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed jUnary gUnary mapRoute
  have returnUnary : UnaryHistory returnRead :=
    unary_cont_closed mapUnary rUnary returnRoute
  have bisectionUnary : UnaryHistory bisectionRead :=
    unary_cont_closed returnUnary bUnary bisectionRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bisectionUnary wUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have mapExact : hsame mapRead (append J G) :=
    mapRoute
  have returnExact : hsame returnRead (append (append J G) R) :=
    returnRoute.trans (congrArg (fun row => append row R) mapExact)
  have bisectionExact : hsame bisectionRead (append (append (append J G) R) B) :=
    bisectionRoute.trans (congrArg (fun row => append row B) returnExact)
  have windowExact : hsame windowRead (append (append (append (append J G) R) B) W) :=
    windowRoute.trans (congrArg (fun row => append row W) bisectionExact)
  have readbackExact : hsame readbackRead
      (append (append (append (append (append J G) R) B) W) Q) :=
    readbackRoute.trans (congrArg (fun row => append row Q) windowExact)
  have sealExact : hsame sealRead
      (append (append (append (append (append (append J G) R) B) W) Q) E) :=
    sealRoute.trans (congrArg (fun row => append row E) readbackExact)
  exact
    ⟨sealExact, mapUnary, returnUnary, bisectionUnary, windowUnary, readbackUnary,
      sealUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp.IntervalReturnRoute
