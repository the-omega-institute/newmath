import BEDC.Derived.LocatedOpenUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedOpenUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LocatedOpen_window_stability
    {L R S Q W E T H C P N transportedWindow : BHist} :
    Cont L R S ->
      Cont S Q W ->
        Cont W E T ->
          hsame transportedWindow W ->
            UnaryHistory L ->
              UnaryHistory R ->
                UnaryHistory Q ->
                  UnaryHistory E ->
                    UnaryHistory W ∧ UnaryHistory transportedWindow ∧ Cont S Q W ∧
                      hsame transportedWindow W := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro sourceRoute windowRoute _sealRoute transportedSame sourceUnary enclosureUnary
    readbackUnary _sealUnary
  have streamUnary : UnaryHistory S :=
    unary_cont_closed sourceUnary enclosureUnary sourceRoute
  have windowUnary : UnaryHistory W :=
    unary_cont_closed streamUnary readbackUnary windowRoute
  have transportedUnary : UnaryHistory transportedWindow :=
    unary_transport_symm windowUnary transportedSame
  exact ⟨windowUnary, transportedUnary, windowRoute, transportedSame⟩

end BEDC.Derived.LocatedOpenUp
