import BEDC.Derived.CompactIntervalFixedPointUp.ResidualBisectionHandoff

namespace BEDC.Derived.CompactIntervalFixedPointUp.BisectionWindowMonotonicity

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactIntervalFixedPointBisectionWindowMonotonicity [AskSetup] [PackageSetup]
    {B W Q E windowRead narrowedWindow readbackRead sealRead : BHist} :
    UnaryHistory B →
      UnaryHistory W →
        UnaryHistory Q →
          UnaryHistory E →
            Cont B W windowRead →
              Cont windowRead W narrowedWindow →
                Cont narrowedWindow Q readbackRead →
                  Cont readbackRead E sealRead →
                    hsame sealRead (append (append (append (append B W) W) Q) E) ∧
                      UnaryHistory narrowedWindow ∧ UnaryHistory readbackRead ∧
                        UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame append UnaryHistory
  intro bUnary wUnary qUnary eUnary windowRoute narrowedRoute readbackRoute sealRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed bUnary wUnary windowRoute
  have narrowedUnary : UnaryHistory narrowedWindow :=
    unary_cont_closed windowUnary wUnary narrowedRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed narrowedUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have windowExact : hsame windowRead (append B W) :=
    windowRoute
  have narrowedExact : hsame narrowedWindow (append (append B W) W) :=
    narrowedRoute.trans (congrArg (fun row => append row W) windowExact)
  have readbackExact : hsame readbackRead (append (append (append B W) W) Q) :=
    readbackRoute.trans (congrArg (fun row => append row Q) narrowedExact)
  have sealExact : hsame sealRead (append (append (append (append B W) W) Q) E) :=
    sealRoute.trans (congrArg (fun row => append row E) readbackExact)
  exact ⟨sealExact, narrowedUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.CompactIntervalFixedPointUp.BisectionWindowMonotonicity
