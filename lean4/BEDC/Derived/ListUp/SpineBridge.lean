import BEDC.Derived.ListUp.AppendContext
import BEDC.Derived.ListUp.FramedEndpoint
import BEDC.Derived.ListUp.Length
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

theorem ListSpineRep_self_classifier {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (cert : NameCert A Rel) {p : BHist} {xs : ListCarrier BHist} :
    ListSpineRep A p xs -> ListClassifierSpec Rel xs xs := by
  intro rep
  induction rep with
  | nil _endpoint =>
      constructor
  | cons head _tail _spine _endpoint ih =>
      constructor
      · exact cert.equiv_refl head
      · exact ih

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

theorem ListSpineBridgeClassifier_public_prefix_append_left_cancel {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (boundary :
      forall {m a a' t t' p p' : BHist} {xs xs' : ListCarrier BHist},
        A a -> A a' -> ListSpineRep A t xs -> ListSpineRep A t' xs' ->
          Cont a t p -> Cont a' t' p' -> hsame m (BHist.e1 p) ->
            hsame m (BHist.e1 p') -> Rel a a' ∧ ListClassifierSpec Rel xs xs')
    {p h k t u : BHist} {xs ys zs : ListCarrier BHist} :
    ListSpineRep A p xs -> ListSpineRep A h (xs ++ ys) ->
      ListSpineRep A k (xs ++ zs) -> ListSpineBridgeClassifier A Rel h k ->
        ListClassifierSpec Rel ys zs ∧
          (ListSpineRep A t ys -> ListSpineRep A u zs ->
            ListSpineBridgeClassifier A Rel t u) := by
  intro prefixRep leftRep rightRep bridge
  have coherent :
      forall {h : BHist} {xs ys : ListCarrier BHist},
        ListSpineRep A h xs -> ListSpineRep A h ys -> ListClassifierSpec Rel xs ys :=
    BEDC.Derived.ListUp.ListSpineRep_coherent_from_cons_boundary boundary
  have prefixClass : ListClassifierSpec Rel xs xs :=
    coherent prefixRep prefixRep
  cases bridge with
  | intro bridgeLeft bridgeTail =>
      cases bridgeTail with
      | intro bridgeRight bridgeData =>
          cases bridgeData with
          | intro bridgeLeftRep bridgeRest =>
              cases bridgeRest with
              | intro bridgeRightRep bridgeClass =>
                  have leftAlign : ListClassifierSpec Rel (xs ++ ys) bridgeLeft :=
                    coherent leftRep bridgeLeftRep
                  have rightAlign : ListClassifierSpec Rel bridgeRight (xs ++ zs) :=
                    coherent bridgeRightRep rightRep
                  have toBridgeRight : ListClassifierSpec Rel (xs ++ ys) bridgeRight :=
                    ListClassifierSpec_trans_from_nameCert cert leftAlign bridgeClass
                  have appended : ListClassifierSpec Rel (xs ++ ys) (xs ++ zs) :=
                    ListClassifierSpec_trans_from_nameCert cert toBridgeRight rightAlign
                  have tails : ListClassifierSpec Rel ys zs :=
                    ListClassifierSpec_BHist_append_left_cancel_classified prefixClass appended
                  constructor
                  · exact tails
                  · intro tailLeftRep tailRightRep
                    exact Exists.intro ys
                      (Exists.intro zs
                        (And.intro tailLeftRep (And.intro tailRightRep tails)))

theorem ListSpineRep_cons_boundary_length_deterministic {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop}
    (boundary :
      forall {m a a' t t' p p' : BHist} {xs xs' : ListCarrier BHist},
        A a -> A a' -> ListSpineRep A t xs -> ListSpineRep A t' xs' ->
          Cont a t p -> Cont a' t' p' -> hsame m (BHist.e1 p) ->
            hsame m (BHist.e1 p') -> Rel a a' ∧ ListClassifierSpec Rel xs xs')
    {m : BHist} {xs ys : ListCarrier BHist} :
    ListSpineRep A m xs -> ListSpineRep A m ys -> xs.length = ys.length := by
  intro repX repY
  have coherent :
      forall {h : BHist} {xs ys : ListCarrier BHist},
        ListSpineRep A h xs -> ListSpineRep A h ys -> ListClassifierSpec Rel xs ys :=
    BEDC.Derived.ListUp.ListSpineRep_coherent_from_cons_boundary boundary
  exact ListClassifierSpec_length_eq (coherent repX repY)

theorem ListSpineBridgeClassifier_public_cons_readback_deterministic {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop}
    (boundary :
      forall {m a a' t t' p p' : BHist} {xs xs' : ListCarrier BHist},
        A a -> A a' -> ListSpineRep A t xs -> ListSpineRep A t' xs' ->
          Cont a t p -> Cont a' t' p' -> hsame m (BHist.e1 p) ->
            hsame m (BHist.e1 p') -> Rel a a' ∧ ListClassifierSpec Rel xs xs')
    {m a a' t t' p p' : BHist} :
    A a -> A a' -> ListSpineHistoryCarrier A t -> ListSpineHistoryCarrier A t' ->
      Cont a t p -> Cont a' t' p' -> hsame m (BHist.e1 p) ->
        hsame m (BHist.e1 p') -> Rel a a' ∧ ListSpineBridgeClassifier A Rel t t' := by
  intro sourceA sourceA' carrierT carrierT' leftCont rightCont sameLeft sameRight
  cases carrierT with
  | intro xs repT =>
      cases carrierT' with
      | intro xs' repT' =>
          have readback :=
            boundary sourceA sourceA' repT repT' leftCont rightCont sameLeft sameRight
          exact And.intro readback.left
            (Exists.intro xs
              (Exists.intro xs'
                (And.intro repT (And.intro repT' readback.right))))

theorem ListSpineBridgeClassifier_represented_spine_alignment {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (coherent :
      forall {h : BHist} {xs ys : ListCarrier BHist},
        ListSpineRep A h xs -> ListSpineRep A h ys -> ListClassifierSpec Rel xs ys)
    {h k : BHist} {xs0 ys0 : ListCarrier BHist} :
    ListSpineRep A h xs0 -> ListSpineRep A k ys0 ->
      ListSpineBridgeClassifier A Rel h k -> ListClassifierSpec Rel xs0 ys0 := by
  intro repH repK bridge
  cases bridge with
  | intro xs bridgeTail =>
      cases bridgeTail with
      | intro ys bridgeData =>
          cases bridgeData with
          | intro repHX bridgeRest =>
              cases bridgeRest with
              | intro repKY classifiedBridge =>
                  have classifiedLeft : ListClassifierSpec Rel xs0 xs :=
                    coherent repH repHX
                  have classifiedRight : ListClassifierSpec Rel ys ys0 :=
                    coherent repKY repK
                  exact ListClassifierSpec_trans_from_nameCert cert
                    (ListClassifierSpec_trans_from_nameCert cert classifiedLeft
                      classifiedBridge)
                    classifiedRight

theorem ListSpineBridgeClassifier_displayed_spine_exactness
    {A : BHist -> Prop} {Rel : BHist -> BHist -> Prop}
    (cert : NameCert A Rel)
    (coherent : forall {h : BHist} {xs ys : ListCarrier BHist},
      ListSpineRep A h xs -> ListSpineRep A h ys -> ListClassifierSpec Rel xs ys)
    {h k : BHist} {xs0 ys0 : ListCarrier BHist} :
    ListSpineRep A h xs0 -> ListSpineRep A k ys0 ->
      (ListSpineBridgeClassifier A Rel h k ↔ ListClassifierSpec Rel xs0 ys0) := by
  intro repH repK
  constructor
  · intro bridge
    exact ListSpineBridgeClassifier_represented_spine_alignment cert coherent repH repK bridge
  · intro classified
    exact Exists.intro xs0
      (Exists.intro ys0 (And.intro repH (And.intro repK classified)))

theorem ListSpineBridgeClassifier_nil_classifier_inversion {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (coherent :
      forall {h : BHist} {xs ys : ListCarrier BHist},
        ListSpineRep A h xs -> ListSpineRep A h ys -> ListClassifierSpec Rel xs ys)
    {h k : BHist} {xs ys : ListCarrier BHist} :
    (ListSpineRep A h [] -> ListSpineRep A k ys ->
      ListSpineBridgeClassifier A Rel h k -> ys = []) ∧
      (ListSpineRep A h xs -> ListSpineRep A k [] ->
        ListSpineBridgeClassifier A Rel h k -> xs = []) := by
  constructor
  · intro repNil repY bridge
    have classified :
        ListClassifierSpec Rel ([] : ListCarrier BHist) ys :=
      ListSpineBridgeClassifier_represented_spine_alignment cert coherent repNil repY bridge
    cases ys with
    | nil =>
        rfl
    | cons _ _ =>
        cases classified
  · intro repX repNil bridge
    have classified :
        ListClassifierSpec Rel xs ([] : ListCarrier BHist) :=
      ListSpineBridgeClassifier_represented_spine_alignment cert coherent repX repNil bridge
    cases xs with
    | nil =>
        rfl
    | cons _ _ =>
        cases classified

end BEDC.Derived.ListUp
