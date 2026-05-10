import BEDC.Derived.IntUp

namespace BEDC.Derived.IntUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem IntUp_StdBridge :
    (forall {sign : BEDC.FKernel.Mark.BMark} {magnitude : BHist},
      IntCarrier sign magnitude ->
        (sign = BEDC.FKernel.Mark.BMark.b0 ∨ sign = BEDC.FKernel.Mark.BMark.b1) ∧
          UnaryHistory magnitude) ∧
      (forall {x y : BEDC.FKernel.Mark.BMark × BHist},
        IntClassifierSpec x y ->
          IntCarrier x.1 x.2 ∧ IntCarrier y.1 y.2 ∧
            BEDC.FKernel.Mark.msame x.1 y.1 ∧ hsame x.2 y.2) ∧
      (forall {p n q m : BHist},
        IntPairClassifier (p, n) (q, m) ->
          IntPairCarrier p n ∧ IntPairCarrier q m ∧
            hsame (BEDC.FKernel.Cont.append p m) (BEDC.FKernel.Cont.append q n)) := by
  constructor
  · intro sign magnitude carrier
    cases carrier with
    | intro signCases magnitudeUnary =>
        exact And.intro signCases magnitudeUnary
  · constructor
    · intro x y classified
      cases classified with
      | intro carrierX rest =>
          cases rest with
          | intro carrierY sameData =>
              cases sameData with
              | intro sameSign sameMagnitude =>
                  exact And.intro carrierX
                    (And.intro carrierY (And.intro sameSign sameMagnitude))
    · intro p n q m classified
      cases classified with
      | intro carrierPN rest =>
          cases rest with
          | intro carrierQM sameDifference =>
              exact And.intro carrierPN (And.intro carrierQM sameDifference)

end BEDC.Derived.IntUp
