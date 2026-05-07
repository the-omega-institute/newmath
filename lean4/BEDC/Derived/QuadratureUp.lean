import BEDC.Derived.NatUp

namespace BEDC.Derived.QuadratureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

def QuadratureDegBoundLe (e d : BHist) : Prop :=
  UnaryHistory e ∧ UnaryHistory d ∧
    forall {k : BHist}, UnaryHistory k -> NatUnaryStrictPrefix d k ->
      NatUnaryStrictPrefix e k

theorem QuadratureDegBoundLe_trans {e d c : BHist} :
    QuadratureDegBoundLe e d -> QuadratureDegBoundLe d c -> QuadratureDegBoundLe e c := by
  intro left right
  constructor
  · exact left.left
  · constructor
    · exact right.right.left
    · intro k unaryK strictCK
      exact left.right.right unaryK (right.right.right unaryK strictCK)

end BEDC.Derived.QuadratureUp
