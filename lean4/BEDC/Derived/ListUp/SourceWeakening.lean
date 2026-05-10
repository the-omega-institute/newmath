import BEDC.Derived.ListUp.HistoryCarrier
import BEDC.Derived.ListUp.SpineBridge

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ListSourceClassifier_weakening {A B : BHist -> Prop}
    {RelA RelB : BHist -> BHist -> Prop} :
    (forall a : BHist, A a -> B a) ->
      (forall a b : BHist, RelA a b -> RelB a b) ->
        (forall {h : BHist}, ListHistoryCarrier A h -> ListHistoryCarrier B h) ∧
          (forall {h k : BHist}, ListHistoryClassifierRec A RelA h k ->
            ListHistoryClassifierRec B RelB h k) ∧
            (forall {h : BHist} {xs : ListCarrier BHist}, ListSpineRep A h xs ->
              ListSpineRep B h xs) ∧
              (forall {h k : BHist}, ListSpineBridgeClassifier A RelA h k ->
                ListSpineBridgeClassifier B RelB h k) ∧
                (forall {h a t p : BHist} {xs : ListCarrier BHist}, A a ->
                  ListSpineRep A t xs -> Cont a t p -> hsame h (BHist.e1 p) ->
                    ListSpineRep B h (a :: xs)) := by
  intro carrierIncl relIncl
  have refineCarrier :
      forall {h : BHist}, ListHistoryCarrier A h -> ListHistoryCarrier B h := by
    intro h carrier
    induction carrier with
    | nil empty =>
        exact ListHistoryCarrier.nil empty
    | cons source tail continuation endpoint tailRefined =>
        exact ListHistoryCarrier.cons (carrierIncl _ source) tailRefined continuation endpoint
  have refineClassifier :
      forall {h k : BHist}, ListHistoryClassifierRec A RelA h k ->
        ListHistoryClassifierRec B RelB h k := by
    intro h k classifier
    induction classifier with
    | nil_nil emptyH emptyK =>
        exact ListHistoryClassifierRec.nil_nil emptyH emptyK
    | cons_cons sourceA sourceB sameAB tailClassifier contA contB endH endK tailRefined =>
        exact ListHistoryClassifierRec.cons_cons (carrierIncl _ sourceA)
          (carrierIncl _ sourceB) (relIncl _ _ sameAB) tailRefined contA contB endH endK
  have refineSpine :
      forall {h : BHist} {xs : ListCarrier BHist}, ListSpineRep A h xs ->
        ListSpineRep B h xs := by
    intro h xs rep
    induction rep with
    | nil empty =>
        exact ListSpineRep.nil empty
    | cons source tail continuation endpoint tailRefined =>
        exact ListSpineRep.cons (carrierIncl _ source) tailRefined continuation endpoint
  have refineListClassifier :
      forall {xs ys : ListCarrier BHist}, ListClassifierSpec RelA xs ys ->
        ListClassifierSpec RelB xs ys := by
    intro xs
    induction xs with
    | nil =>
        intro ys classified
        cases ys with
        | nil =>
            constructor
        | cons _ _ =>
            cases classified
    | cons x xs ih =>
        intro ys classified
        cases ys with
        | nil =>
            cases classified
        | cons y ys =>
            cases classified with
            | intro head tail =>
                exact And.intro (relIncl x y head) (ih tail)
  have refineBridge :
      forall {h k : BHist}, ListSpineBridgeClassifier A RelA h k ->
        ListSpineBridgeClassifier B RelB h k := by
    intro h k bridge
    cases bridge with
    | intro xs bridgeTail =>
        cases bridgeTail with
        | intro ys bridgeData =>
            cases bridgeData with
            | intro leftRep bridgeRest =>
                cases bridgeRest with
                | intro rightRep classified =>
                    exact Exists.intro xs
                      (Exists.intro ys
                        (And.intro (refineSpine leftRep)
                          (And.intro (refineSpine rightRep)
                            (refineListClassifier classified))))
  constructor
  · exact refineCarrier
  · constructor
    · exact refineClassifier
    · constructor
      · exact refineSpine
      · constructor
        · exact refineBridge
        · intro h a t p xs source tailRep continuation endpoint
          exact ListSpineRep.cons (carrierIncl a source) (refineSpine tailRep)
            continuation endpoint

end BEDC.Derived.ListUp
