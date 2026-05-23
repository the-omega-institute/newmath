import BEDC.Derived.RegularCauchyWitnessSelectorUp.TasteGate
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.RegularCauchyWitnessSelectorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem RegularCauchyWitnessSelector_ledger_nonescape
    {M W T R E H terminalRead hostTail : BHist} :
    Cont M W H ->
      Cont H T R ->
        Cont R E terminalRead ->
          (Cont terminalRead (BHist.e0 hostTail) M -> False) ∧
            (Cont terminalRead (BHist.e1 hostTail) M -> False) := by
  -- BEDC touchpoint anchor: BHist Cont
  intro modulusWindow windowTolerance toleranceReadback
  have sourceReadback : Cont M (append W T) R := by
    calc
      R = append H T := windowTolerance
      _ = append (append M W) T := congrArg (fun row => append row T) modulusWindow
      _ = append M (append W T) := append_assoc M W T
  have sourceTerminal : Cont M (append (append W T) E) terminalRead := by
    calc
      terminalRead = append R E := toleranceReadback
      _ = append (append M (append W T)) E :=
        congrArg (fun row => append row E) sourceReadback
      _ = append M (append (append W T) E) := append_assoc M (append W T) E
  exact
    ⟨fun escape => cont_mutual_extension_right_tail_absurd.left sourceTerminal escape,
      fun escape => cont_mutual_extension_right_tail_absurd.right sourceTerminal escape⟩

end BEDC.Derived.RegularCauchyWitnessSelectorUp
