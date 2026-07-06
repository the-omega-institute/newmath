import BEDC.Derived.DeGiorgiIterationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DeGiorgiIterationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DeGiorgiIterationCarrier_energy_decay_handoff [AskSetup] [PackageSetup]
    {L T S P M B Q R H C G N levelRead controlRead budgetRead sealRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory T ->
        UnaryHistory S ->
          UnaryHistory P ->
            UnaryHistory M ->
              UnaryHistory B ->
                UnaryHistory Q ->
                  UnaryHistory R ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        UnaryHistory G ->
                          UnaryHistory N ->
                            Cont L T levelRead ->
                              Cont S P controlRead ->
                                Cont M B budgetRead ->
                                  Cont Q R sealRead ->
                                    Cont C N nameRead ->
                                      PkgSig bundle G pkg ->
                                        PkgSig bundle N pkg ->
                                          UnaryHistory levelRead ∧
                                            UnaryHistory controlRead ∧
                                              UnaryHistory budgetRead ∧
                                                UnaryHistory sealRead ∧
                                                  UnaryHistory nameRead ∧
                                                    Cont L T levelRead ∧
                                                      Cont S P controlRead ∧
                                                        Cont M B budgetRead ∧
                                                          Cont Q R sealRead ∧
                                                            Cont C N nameRead ∧
                                                              PkgSig bundle G pkg ∧
                                                                PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro LUnary TUnary SUnary PUnary MUnary BUnary QUnary RUnary _HUnary CUnary
    _GUnary NUnary levelRoute controlRoute budgetRoute sealRoute nameRoute provenancePkg
    namePkg
  have levelReadUnary : UnaryHistory levelRead :=
    unary_cont_closed LUnary TUnary levelRoute
  have controlReadUnary : UnaryHistory controlRead :=
    unary_cont_closed SUnary PUnary controlRoute
  have budgetReadUnary : UnaryHistory budgetRead :=
    unary_cont_closed MUnary BUnary budgetRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed QUnary RUnary sealRoute
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed CUnary NUnary nameRoute
  exact
    ⟨levelReadUnary, controlReadUnary, budgetReadUnary, sealReadUnary, nameReadUnary,
      levelRoute, controlRoute, budgetRoute, sealRoute, nameRoute, provenancePkg, namePkg⟩

end BEDC.Derived.DeGiorgiIterationUp
