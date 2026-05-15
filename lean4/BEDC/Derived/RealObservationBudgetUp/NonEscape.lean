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

theorem RealObservationBudgetUp_nonescape [AskSetup] [PackageSetup]
    {packet : RealObservationBudgetUp} {E W D R S H C P N consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    packet = RealObservationBudgetUp.mk E W D R S H C P N →
      UnaryHistory E →
        UnaryHistory W →
          UnaryHistory R →
            UnaryHistory H →
              UnaryHistory P →
                Cont E W D →
                  Cont D R S →
                    Cont S H C →
                      Cont C P consumer →
                        PkgSig bundle N pkg →
                          PkgSig bundle consumer pkg →
                            (∃ observed : RealObservationBudgetUp,
                              observed = packet ∧
                                UnaryHistory D ∧
                                UnaryHistory S ∧
                                UnaryHistory C ∧
                                UnaryHistory consumer ∧
                                Cont E W D ∧
                                Cont D R S ∧
                                Cont S H C ∧
                                Cont C P consumer ∧
                                PkgSig bundle N pkg ∧
                                PkgSig bundle consumer pkg) := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg Cont UnaryHistory
  intro packetShape eUnary wUnary rUnary hUnary pUnary ewd drs shc cpConsumer nPkg
    consumerPkg
  have dUnary : UnaryHistory D :=
    unary_cont_closed eUnary wUnary ewd
  have sUnary : UnaryHistory S :=
    unary_cont_closed dUnary rUnary drs
  have cUnary : UnaryHistory C :=
    unary_cont_closed sUnary hUnary shc
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed cUnary pUnary cpConsumer
  exact
    Exists.intro packet
      ⟨rfl, dUnary, sUnary, cUnary, consumerUnary, ewd, drs, shc, cpConsumer, nPkg,
        consumerPkg⟩

end BEDC.Derived.RealObservationBudgetUp
