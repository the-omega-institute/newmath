import BEDC.Derived.ListUp

namespace BEDC.Derived.ListUp

theorem ListClassifierSpec_case_exactness
    {sameA : BEDC.FKernel.Hist.BHist -> BEDC.FKernel.Hist.BHist -> Prop} :
    ListClassifierSpec sameA ([] : ListCarrier BEDC.FKernel.Hist.BHist) [] /\
      (forall {a b : BEDC.FKernel.Hist.BHist} {xs ys : ListCarrier BEDC.FKernel.Hist.BHist},
        ListClassifierSpec sameA (a :: xs) (b :: ys) <->
          sameA a b /\ ListClassifierSpec sameA xs ys) /\
        (forall {b : BEDC.FKernel.Hist.BHist} {ys : ListCarrier BEDC.FKernel.Hist.BHist},
          ListClassifierSpec sameA ([] : ListCarrier BEDC.FKernel.Hist.BHist) (b :: ys) ->
            False) /\
          (forall {a : BEDC.FKernel.Hist.BHist} {xs : ListCarrier BEDC.FKernel.Hist.BHist},
            ListClassifierSpec sameA (a :: xs) ([] : ListCarrier BEDC.FKernel.Hist.BHist) ->
              False) := by
  constructor
  · change ListClassifierSpec sameA ([] : ListCarrier BEDC.FKernel.Hist.BHist) []
    constructor
  · constructor
    · intro a b xs ys
      constructor
      · intro classifier
        exact classifier
      · intro data
        exact data
    · constructor
      · intro b ys classifier
        cases classifier
      · intro a xs classifier
        cases classifier

end BEDC.Derived.ListUp
