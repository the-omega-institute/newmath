import BEDC.Derived.RealObservationBudgetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealObservationBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealObservationBudgetUp_StdBridge [AskSetup] [PackageSetup]
    {packet : RealObservationBudgetUp} {E W D R S H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    packet = RealObservationBudgetUp.mk E W D R S H C P N →
      UnaryHistory E →
        UnaryHistory W →
          UnaryHistory D →
            UnaryHistory R →
              UnaryHistory H →
                UnaryHistory P →
                  Cont E W D →
                    Cont D R S →
                      Cont S H C →
                        Cont C P publicRead →
                          PkgSig bundle N pkg →
                            PkgSig bundle publicRead pkg →
                              UnaryHistory D ∧ UnaryHistory S ∧ UnaryHistory C ∧
                                UnaryHistory publicRead ∧ Cont E W D ∧ Cont D R S ∧
                                  Cont S H C ∧ Cont C P publicRead ∧
                                    PkgSig bundle N pkg ∧
                                      PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont UnaryHistory
  intro packetShape eUnary wUnary _dUnary rUnary hUnary pUnary ewd drs shc
    cpPublic nPkg publicPkg
  cases packetShape
  have dUnary : UnaryHistory D :=
    unary_cont_closed eUnary wUnary ewd
  have sUnary : UnaryHistory S :=
    unary_cont_closed dUnary rUnary drs
  have cUnary : UnaryHistory C :=
    unary_cont_closed sUnary hUnary shc
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed cUnary pUnary cpPublic
  exact
    ⟨dUnary, sUnary, cUnary, publicUnary, ewd, drs, shc, cpPublic, nPkg, publicPkg⟩

end BEDC.Derived.RealObservationBudgetUp
