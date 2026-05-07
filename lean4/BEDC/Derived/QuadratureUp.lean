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

theorem QuadratureDegBoundLe_preorder_rows :
    (forall {d : BHist}, UnaryHistory d -> QuadratureDegBoundLe d d) ∧
      (forall {e d c : BHist}, QuadratureDegBoundLe e d -> QuadratureDegBoundLe d c ->
        QuadratureDegBoundLe e c) := by
  constructor
  · intro d unaryD
    constructor
    · exact unaryD
    · constructor
      · exact unaryD
      · intro k _unaryK strictDK
        exact strictDK
  · intro e d c left right
    exact QuadratureDegBoundLe_trans left right

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

def QuadratureExactUpTo (qExact : BHist -> Prop) (coeff : BHist -> BHist)
    (zero d : BHist) : Prop :=
  UnaryHistory zero ∧ UnaryHistory d ∧
    forall {p : BHist},
      (UnaryHistory zero ∧ UnaryHistory d ∧
        (forall {k : BHist}, UnaryHistory k -> NatUnaryStrictPrefix d k ->
          hsame (coeff k) zero)) ->
        qExact p

theorem QuadratureExactUpTo_weakening {qExact : BHist -> Prop} {coeff : BHist -> BHist}
    {zero e d : BHist} :
    QuadratureDegBoundLe e d -> QuadratureExactUpTo qExact coeff zero d ->
      UnaryHistory zero ∧ UnaryHistory e ∧
        forall {p : BHist},
          (UnaryHistory zero ∧ UnaryHistory e ∧
            (forall {k : BHist}, UnaryHistory k -> NatUnaryStrictPrefix e k ->
              hsame (coeff k) zero)) ->
            qExact p := by
  intro bound exactD
  constructor
  · exact exactD.left
  · constructor
    · exact bound.left
    · intro p windowE
      exact exactD.right.right
        (QuadraturePolynomialDegreeWindow_inclusion bound windowE)

theorem QuadratureExactUpTo_degree_equivalence_stability {qExact : BHist -> Prop}
    {coeff : BHist -> BHist} {zero e d : BHist} :
    QuadratureDegBoundLe e d -> QuadratureDegBoundLe d e ->
      (QuadratureExactUpTo qExact coeff zero d ↔ QuadratureExactUpTo qExact coeff zero e) ∧
        UnaryHistory d ∧ UnaryHistory e := by
  intro ed de
  have forward :
      QuadratureExactUpTo qExact coeff zero d ->
        QuadratureExactUpTo qExact coeff zero e := by
    intro exactD
    exact QuadratureExactUpTo_weakening ed exactD
  have backward :
      QuadratureExactUpTo qExact coeff zero e ->
        QuadratureExactUpTo qExact coeff zero d := by
    intro exactE
    exact QuadratureExactUpTo_weakening de exactE
  exact And.intro (Iff.intro forward backward) (And.intro ed.right.left ed.left)

end BEDC.Derived.QuadratureUp
