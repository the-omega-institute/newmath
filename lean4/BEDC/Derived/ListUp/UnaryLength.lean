import BEDC.Derived.ListUp
import BEDC.Derived.ListUp.FramedEndpoint
import BEDC.FKernel.Cont

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

def ListUnaryLength : ListCarrier BHist -> BHist
  | [] => BHist.Empty
  | _ :: xs => BHist.e1 (ListUnaryLength xs)

theorem ListUnaryLength_append_cont {xs ys : ListCarrier BHist} :
    Cont (ListUnaryLength ys) (ListUnaryLength xs) (ListUnaryLength (xs ++ ys)) := by
  induction xs with
  | nil =>
      exact cont_right_unit (ListUnaryLength ys)
  | cons _ xs ih =>
      exact cont_step_one ih

theorem ListClassifierSpec_unary_length_token_hsame :
    forall {xs ys : ListCarrier BHist},
      ListClassifierSpec hsame xs ys -> hsame (ListUnaryLength xs) (ListUnaryLength ys) := by
  intro xs
  induction xs with
  | nil =>
      intro ys classified
      cases ys with
      | nil =>
          exact hsame_refl BHist.Empty
      | cons y ys =>
          cases classified
  | cons x xs ih =>
      intro ys classified
      cases ys with
      | nil =>
          cases classified
      | cons y ys =>
          cases classified with
          | intro sameHead sameTail =>
              exact hsame_e1_congr (ih sameTail)

def ListPublicUnaryLength (A : BHist -> Prop) (h u : BHist) : Prop :=
  ∃ xs : ListCarrier BHist, FramedListSpineRep A h xs ∧ hsame (ListUnaryLength xs) u

theorem ListPublicUnaryLength_classifier_transport {A : BHist -> Prop}
    {Rel : BHist -> BHist -> Prop} (cert : NameCert A Rel)
    (compat : ListSourceHsameCompatible A Rel)
    (relToHsame : forall {a b : BHist}, Rel a b -> hsame a b) {h k u : BHist} :
    FramedListBridgeClassifier A Rel h k ->
      (ListPublicUnaryLength A h u -> ListPublicUnaryLength A k u) ∧
        (ListPublicUnaryLength A k u -> ListPublicUnaryLength A h u) := by
  intro bridge
  have listRelToHsame :
      forall {xs ys : ListCarrier BHist},
        ListClassifierSpec Rel xs ys -> ListClassifierSpec hsame xs ys := by
    intro xs
    induction xs with
    | nil =>
        intro ys classified
        cases ys with
        | nil =>
            constructor
        | cons _ _ =>
            cases classified
    | cons x tail ih =>
        intro ys classified
        cases ys with
        | nil =>
            cases classified
        | cons y ysTail =>
            cases classified with
            | intro headRel tailRel =>
                exact And.intro (relToHsame headRel) (ih tailRel)
  cases bridge with
  | intro xs bridgeTail =>
      cases bridgeTail with
      | intro ys bridgeData =>
          cases bridgeData with
          | intro repH bridgeRest =>
              cases bridgeRest with
              | intro repK classifiedBridge =>
                  constructor
                  · intro publicH
                    cases publicH with
                    | intro xsH publicData =>
                        have classifiedLeft : ListClassifierSpec Rel xsH xs :=
                          FramedListSpineRep_coherence compat publicData.left repH
                        have classifiedRel : ListClassifierSpec Rel xsH ys :=
                          ListClassifierSpec_trans_from_nameCert cert classifiedLeft classifiedBridge
                        have classifiedHsame : ListClassifierSpec hsame xsH ys :=
                          listRelToHsame classifiedRel
                        have sameLength :
                            hsame (ListUnaryLength ys) u :=
                          hsame_trans
                            (hsame_symm
                              (ListClassifierSpec_unary_length_token_hsame classifiedHsame))
                            publicData.right
                        exact Exists.intro ys (And.intro repK sameLength)
                  · intro publicK
                    cases publicK with
                    | intro ysK publicData =>
                        have classifiedLeft : ListClassifierSpec Rel ysK ys :=
                          FramedListSpineRep_coherence compat publicData.left repK
                        have classifiedForward : ListClassifierSpec Rel ys xs :=
                          ListClassifierSpec_symm_from_nameCert cert classifiedBridge
                        have classifiedRel : ListClassifierSpec Rel ysK xs :=
                          ListClassifierSpec_trans_from_nameCert cert classifiedLeft
                            classifiedForward
                        have classifiedHsame : ListClassifierSpec hsame ysK xs :=
                          listRelToHsame classifiedRel
                        have sameLength :
                            hsame (ListUnaryLength xs) u :=
                          hsame_trans
                            (hsame_symm
                              (ListClassifierSpec_unary_length_token_hsame classifiedHsame))
                            publicData.right
                        exact Exists.intro xs (And.intro repH sameLength)

end BEDC.Derived.ListUp
