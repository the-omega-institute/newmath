import BEDC.Derived.NatUp

namespace BEDC.Derived.QuadratureUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatUp

def QuadratureCarriedRuleSourceRow
    (xs alpha omega integral poly degree row : BHist) : Prop :=
  UnaryHistory xs ∧ UnaryHistory alpha ∧ UnaryHistory omega ∧ UnaryHistory integral ∧
    UnaryHistory poly ∧ UnaryHistory degree ∧
      Cont xs (append alpha (append omega integral)) row

theorem QuadratureCarriedRuleSourceRow_scope
    {xs alpha omega integral poly degree row endpoint : BHist} :
    QuadratureCarriedRuleSourceRow xs alpha omega integral poly degree row ->
      Cont row poly endpoint ->
        UnaryHistory xs ∧ UnaryHistory alpha ∧ UnaryHistory omega ∧ UnaryHistory integral ∧
          UnaryHistory poly ∧ UnaryHistory degree ∧ UnaryHistory endpoint ∧
            Cont row poly endpoint := by
  intro rowData endpointCont
  have tailUnary : UnaryHistory (append alpha (append omega integral)) :=
    unary_append_closed rowData.right.left
      (unary_append_closed rowData.right.right.left rowData.right.right.right.left)
  have rowUnary : UnaryHistory row :=
    unary_cont_closed rowData.left tailUnary rowData.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed rowUnary rowData.right.right.right.right.left endpointCont
  exact And.intro rowData.left
    (And.intro rowData.right.left
      (And.intro rowData.right.right.left
        (And.intro rowData.right.right.right.left
          (And.intro rowData.right.right.right.right.left
            (And.intro rowData.right.right.right.right.right.left
              (And.intro endpointUnary endpointCont))))))

theorem QuadratureLedgerExactness_surface
    {xs alpha omega integral poly degree row qsum integralValue : BHist} :
    QuadratureCarriedRuleSourceRow xs alpha omega integral poly degree row ->
      Cont row poly qsum -> Cont integral poly integralValue -> hsame qsum integralValue ->
        UnaryHistory qsum ∧ UnaryHistory integralValue ∧ hsame qsum integralValue ∧
          Cont row poly qsum ∧ Cont integral poly integralValue := by
  intro rowData qsumCont integralCont exactSame
  have tailUnary : UnaryHistory (append alpha (append omega integral)) :=
    unary_append_closed rowData.right.left
      (unary_append_closed rowData.right.right.left rowData.right.right.right.left)
  have rowUnary : UnaryHistory row :=
    unary_cont_closed rowData.left tailUnary rowData.right.right.right.right.right.right
  have qsumUnary : UnaryHistory qsum :=
    unary_cont_closed rowUnary rowData.right.right.right.right.left qsumCont
  have integralValueUnary : UnaryHistory integralValue :=
    unary_cont_closed rowData.right.right.right.left rowData.right.right.right.right.left
      integralCont
  exact And.intro qsumUnary
    (And.intro integralValueUnary
      (And.intro exactSame (And.intro qsumCont integralCont)))

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
