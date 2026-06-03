import BEDC.Derived.DecimalExpansionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DecimalExpansionCountableDenseConsumerHandoff [AskSetup] [PackageSetup]
    {D W V Q R E H C P N prefixRead placeRead toleranceRead readbackRead sealRead denseRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory H →
                  UnaryHistory C →
                    Cont D W prefixRead →
                      Cont prefixRead V placeRead →
                        Cont placeRead Q toleranceRead →
                          Cont toleranceRead R readbackRead →
                            Cont readbackRead E sealRead →
                              Cont sealRead H denseRead →
                                Cont denseRead C namedRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      UnaryHistory prefixRead ∧
                                        UnaryHistory placeRead ∧
                                          UnaryHistory toleranceRead ∧
                                            UnaryHistory readbackRead ∧
                                              UnaryHistory sealRead ∧
                                                UnaryHistory denseRead ∧
                                                  UnaryHistory namedRead ∧
                                                    PkgSig bundle P pkg ∧
                                                      PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary hUnary cUnary prefixRoute placeRoute
    toleranceRoute readbackRoute sealRoute denseRoute namedRoute provenancePkg namePkg
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed dUnary wUnary prefixRoute
  have placeUnary : UnaryHistory placeRead :=
    unary_cont_closed prefixUnary vUnary placeRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed placeUnary qUnary toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed sealUnary hUnary denseRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed denseUnary cUnary namedRoute
  exact
    ⟨prefixUnary, placeUnary, toleranceUnary, readbackUnary, sealUnary, denseUnary,
      namedUnary, provenancePkg, namePkg⟩

end BEDC.Derived.DecimalExpansionUp
