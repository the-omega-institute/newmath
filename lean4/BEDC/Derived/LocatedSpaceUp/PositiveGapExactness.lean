import BEDC.Derived.LocatedSpaceUp.PositiveGapExactnessRoute

namespace BEDC.Derived.LocatedSpaceUp.PositiveGapExactness

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LocatedSpaceCarrier_positive_gap_exactness [AskSetup] [PackageSetup]
    {X R A G W Q E H C P N requestRead gapRead windowRead readbackRead sealRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory X →
      UnaryHistory R →
        UnaryHistory A →
          UnaryHistory G →
            UnaryHistory W →
              UnaryHistory Q →
                UnaryHistory E →
                  UnaryHistory H →
                    UnaryHistory C →
                      UnaryHistory P →
                        UnaryHistory N →
                          Cont X R requestRead →
                            Cont A G gapRead →
                              Cont requestRead W windowRead →
                                Cont windowRead Q readbackRead →
                                  Cont readbackRead E sealRead →
                                    Cont sealRead N namedRead →
                                      PkgSig bundle namedRead pkg →
                                        hsame gapRead (append A G) ∧
                                          hsame sealRead
                                            (append (append (append (append X R) W) Q) E) ∧
                                            UnaryHistory gapRead ∧ UnaryHistory sealRead ∧
                                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont append ProbeBundle PkgSig hsame UnaryHistory
  intro xUnary rUnary aUnary gUnary wUnary qUnary eUnary _hUnary _cUnary _pUnary
    nUnary requestCont gapCont windowCont readbackCont sealCont namedCont _namedPkg
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed xUnary rUnary requestCont
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed aUnary gUnary gapCont
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed requestUnary wUnary windowCont
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary qUnary readbackCont
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealCont
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedCont
  have requestExact : hsame requestRead (append X R) :=
    requestCont
  have gapExact : hsame gapRead (append A G) :=
    gapCont
  have windowExact : hsame windowRead (append (append X R) W) :=
    windowCont.trans (congrArg (fun row => append row W) requestExact)
  have readbackExact : hsame readbackRead (append (append (append X R) W) Q) :=
    readbackCont.trans (congrArg (fun row => append row Q) windowExact)
  have sealExact : hsame sealRead (append (append (append (append X R) W) Q) E) :=
    sealCont.trans (congrArg (fun row => append row E) readbackExact)
  exact ⟨gapExact, sealExact, gapUnary, sealUnary, namedUnary⟩

end BEDC.Derived.LocatedSpaceUp.PositiveGapExactness
