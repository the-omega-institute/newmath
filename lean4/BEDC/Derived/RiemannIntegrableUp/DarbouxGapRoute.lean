import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RiemannIntegrableUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem RiemannIntegrableCarrier_darboux_gap_route
    {D M L U G T H C P N dmRead lowerUpperRead gapRead handoffRead : BHist} :
    Cont D M dmRead →
      Cont L U lowerUpperRead →
        Cont lowerUpperRead G gapRead →
          Cont gapRead T handoffRead →
            UnaryHistory D →
              UnaryHistory M →
                UnaryHistory L →
                  UnaryHistory U →
                    UnaryHistory G →
                      UnaryHistory T →
                        UnaryHistory dmRead ∧ UnaryHistory lowerUpperRead ∧
                          UnaryHistory gapRead ∧ UnaryHistory handoffRead ∧
                            Cont D M dmRead ∧ Cont L U lowerUpperRead ∧
                              Cont lowerUpperRead G gapRead ∧
                                Cont gapRead T handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro dmCont lowerUpperCont gapCont handoffCont unaryD unaryM unaryL unaryU unaryG unaryT
  have dmUnary : UnaryHistory dmRead :=
    unary_cont_closed unaryD unaryM dmCont
  have lowerUpperUnary : UnaryHistory lowerUpperRead :=
    unary_cont_closed unaryL unaryU lowerUpperCont
  have gapUnary : UnaryHistory gapRead :=
    unary_cont_closed lowerUpperUnary unaryG gapCont
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed gapUnary unaryT handoffCont
  exact
    ⟨dmUnary, lowerUpperUnary, gapUnary, handoffUnary, dmCont, lowerUpperCont, gapCont,
      handoffCont⟩

end BEDC.Derived.RiemannIntegrableUp
