import BEDC.Derived.NatUp

namespace BEDC.Derived.QuadratureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

def QuadratureDegBoundLe (e d : BHist) : Prop :=
  UnaryHistory e ∧ UnaryHistory d ∧
    forall {k : BHist}, UnaryHistory k -> NatUnaryStrictPrefix d k ->
      NatUnaryStrictPrefix e k

def QuadraturePolynomialWindow (trim : BHist -> BHist -> BHist) (p d : BHist) : Prop :=
  UnaryHistory p ∧ UnaryHistory d ∧
    forall {k : BHist}, UnaryHistory k -> NatUnaryStrictPrefix d k ->
      hsame (trim p k) BHist.Empty

theorem QuadratureDegBoundLe_trans {e d c : BHist} :
    QuadratureDegBoundLe e d -> QuadratureDegBoundLe d c -> QuadratureDegBoundLe e c := by
  intro left right
  constructor
  · exact left.left
  · constructor
    · exact right.right.left
    · intro k unaryK strictCK
      exact left.right.right unaryK (right.right.right unaryK strictCK)

theorem QuadraturePolynomialWindow_inclusion {trim : BHist -> BHist -> BHist}
    {p e d : BHist} :
    QuadratureDegBoundLe e d -> QuadraturePolynomialWindow trim p e ->
      QuadraturePolynomialWindow trim p d ∧ UnaryHistory d := by
  intro degreeBound window
  have windowD : QuadraturePolynomialWindow trim p d := by
    constructor
    · exact window.left
    · constructor
      · exact degreeBound.right.left
      · intro k unaryK strictDK
        exact window.right.right unaryK (degreeBound.right.right unaryK strictDK)
  exact And.intro windowD degreeBound.right.left

end BEDC.Derived.QuadratureUp
