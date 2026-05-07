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

theorem QuadraturePolynomialDegreeWindow_inclusion {coeff : BHist -> BHist} {zero e d : BHist} :
    QuadratureDegBoundLe e d ->
      (UnaryHistory zero ∧ UnaryHistory e ∧
        (forall {k : BHist}, UnaryHistory k -> NatUnaryStrictPrefix e k ->
          hsame (coeff k) zero)) ->
        UnaryHistory zero ∧ UnaryHistory d ∧
          (forall {k : BHist}, UnaryHistory k -> NatUnaryStrictPrefix d k ->
            hsame (coeff k) zero) := by
  intro bound window
  constructor
  · exact window.left
  · constructor
    · exact bound.right.left
    · intro k unaryK strictDK
      exact window.right.right unaryK (bound.right.right unaryK strictDK)

def QuadraturePolyDegLe (coeff : BHist -> BHist -> BHist) (zero p d : BHist) : Prop :=
  UnaryHistory p ∧ UnaryHistory zero ∧ UnaryHistory d ∧
    forall {k : BHist}, UnaryHistory k -> NatUnaryStrictPrefix d k ->
      hsame (coeff p k) zero

def QuadratureExactUpTo (coeff : BHist -> BHist -> BHist) (zero d : BHist)
    (QExact : BHist -> Prop) : Prop :=
  UnaryHistory zero ∧ UnaryHistory d ∧
    forall {p : BHist}, QuadraturePolyDegLe coeff zero p d -> QExact p

theorem QuadratureExactnessDegree_weakening
    {coeff : BHist -> BHist -> BHist} {zero e d : BHist} {QExact : BHist -> Prop} :
    QuadratureDegBoundLe e d -> QuadratureExactUpTo coeff zero d QExact ->
      QuadratureExactUpTo coeff zero e QExact ∧ UnaryHistory e := by
  intro bound exactD
  constructor
  · constructor
    · exact exactD.left
    · constructor
      · exact bound.left
      · intro p degreeE
        have degreeD :
            UnaryHistory zero ∧ UnaryHistory d ∧
              forall {k : BHist}, UnaryHistory k -> NatUnaryStrictPrefix d k ->
                hsame (coeff p k) zero :=
          QuadraturePolynomialDegreeWindow_inclusion (coeff := coeff p)
            (zero := zero) (e := e) (d := d) bound
            (And.intro degreeE.right.left
              (And.intro degreeE.right.right.left degreeE.right.right.right))
        exact exactD.right.right
          (And.intro degreeE.left
            (And.intro degreeD.left
              (And.intro degreeD.right.left degreeD.right.right)))
  · exact bound.left

end BEDC.Derived.QuadratureUp
