import BEDC.Derived.ListUp.FramedEndpoint
import BEDC.Derived.ListUp.SpineCoherence

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def ListSpineBridgeClassifier (A : BHist -> Prop) (Rel : BHist -> BHist -> Prop)
    (h k : BHist) : Prop :=
  exists xs ys : ListCarrier BHist,
    ListSpineRep A h xs ∧ ListSpineRep A k ys ∧ ListClassifierSpec Rel xs ys

def ListSpineHistoryCarrier (A : BHist -> Prop) (h : BHist) : Prop :=
  exists xs : ListCarrier BHist, ListSpineRep A h xs

protected theorem ListSpineBridgeClassifier_stability_from_cons_boundary {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (boundary :
      forall {m a a' t t' p p' : BHist} {xs xs' : ListCarrier BHist},
        A a -> A a' -> ListSpineRep A t xs -> ListSpineRep A t' xs' ->
          Cont a t p -> Cont a' t' p' -> hsame m (BHist.e1 p) ->
            hsame m (BHist.e1 p') -> Rel a a' ∧ ListClassifierSpec Rel xs xs') :
    (forall {h : BHist},
      ListSpineHistoryCarrier A h -> ListSpineBridgeClassifier A Rel h h) ∧
      (forall {h k : BHist},
        ListSpineBridgeClassifier A Rel h k -> ListSpineBridgeClassifier A Rel k h) ∧
        (forall {h k u : BHist},
          ListSpineBridgeClassifier A Rel h k -> ListSpineBridgeClassifier A Rel k u ->
            ListSpineBridgeClassifier A Rel h u) ∧
          (forall {h k : BHist},
            ListSpineBridgeClassifier A Rel h k -> ListSpineHistoryCarrier A k) := by
  have coherent :
      forall {h : BHist} {xs ys : ListCarrier BHist},
        ListSpineRep A h xs -> ListSpineRep A h ys -> ListClassifierSpec Rel xs ys :=
    BEDC.Derived.ListUp.ListSpineRep_coherent_from_cons_boundary boundary
  constructor
  · intro h carrierH
    cases carrierH with
    | intro xs repH =>
        exact Exists.intro xs
          (Exists.intro xs (And.intro repH (And.intro repH (coherent repH repH))))
  · constructor
    · intro h k bridge
      cases bridge with
      | intro xs bridgeTail =>
          cases bridgeTail with
          | intro ys bridgeData =>
              cases bridgeData with
              | intro repH bridgeRest =>
                  cases bridgeRest with
                  | intro repK classified =>
                      exact Exists.intro ys
                        (Exists.intro xs
                          (And.intro repK
                            (And.intro repH
                              (ListClassifierSpec_symm_from_nameCert cert classified))))
    · constructor
      · intro h k u bridgeHK bridgeKU
        cases bridgeHK with
        | intro xs bridgeHKTail =>
            cases bridgeHKTail with
            | intro ys bridgeHKData =>
                cases bridgeHKData with
                | intro repH bridgeHKRest =>
                    cases bridgeHKRest with
                    | intro repKLeft classifiedHK =>
                        cases bridgeKU with
                        | intro ys' bridgeKUTail =>
                            cases bridgeKUTail with
                            | intro zs bridgeKUData =>
                                cases bridgeKUData with
                                | intro repKRight bridgeKURest =>
                                    cases bridgeKURest with
                                    | intro repU classifiedKU =>
                                        have middle : ListClassifierSpec Rel ys ys' :=
                                          coherent repKLeft repKRight
                                        have classifiedHYs' : ListClassifierSpec Rel xs ys' :=
                                          ListClassifierSpec_trans_from_nameCert cert
                                            classifiedHK middle
                                        exact Exists.intro xs
                                          (Exists.intro zs
                                            (And.intro repH
                                              (And.intro repU
                                                (ListClassifierSpec_trans_from_nameCert
                                                  cert classifiedHYs' classifiedKU))))
      · intro h k bridge
        cases bridge with
        | intro xs bridgeTail =>
            cases bridgeTail with
            | intro ys bridgeData =>
                cases bridgeData with
                | intro _repH bridgeRest =>
                    cases bridgeRest with
                    | intro repK _classified =>
                        exact Exists.intro ys repK

end BEDC.Derived.ListUp
