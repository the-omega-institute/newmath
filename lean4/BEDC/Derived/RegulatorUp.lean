import BEDC.FKernel.Cont
import BEDC.FKernel.Hist

namespace BEDC.Derived.RegulatorUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

def RegulatorRootInputPacket
    (D N u iota nu beta delta rho : BHist) : Prop :=
  Cont D u iota ∧
    Cont N nu beta ∧
      hsame (append (append D N) delta) rho

theorem RegulatorRootInputPacket_dependency_layout_unique
    {D N u iota nu beta delta delta' rho : BHist} :
    RegulatorRootInputPacket D N u iota nu beta delta rho ->
      RegulatorRootInputPacket D N u iota nu beta delta' rho ->
        hsame (append (append D N) delta) (append (append D N) delta') ∧
          hsame delta delta' := by
  intro left right
  have sameLayoutRows :
      hsame (append (append D N) delta) (append (append D N) delta') :=
    hsame_trans left.right.right (hsame_symm right.right.right)
  exact And.intro sameLayoutRows (append_left_cancel (h := append D N) sameLayoutRows)

end BEDC.Derived.RegulatorUp
