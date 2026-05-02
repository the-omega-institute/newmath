import BEDC.Derived.OptionUp.PayloadDescentImageClassifier

namespace BEDC.Derived.OptionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_absent_public_factorization
    {S T U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoD : forall a : BHist, S a -> T (delta.map a))
    (rhoE : forall b : BHist, T b -> U (epsilon.map b))
    (epsilon_hsame :
      forall x y : BHist, T x -> T y -> hsame x y ->
        hsame (epsilon.map x) (epsilon.map y))
    (certS : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {m m' u u' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' ->
      hsame m u ->
        hsame m' u' ->
          hsame u BHist.Empty ->
            hsame u' BHist.Empty ->
              exists k k' : BHist,
                TaggedOptionPayloadDescentImageClassifier S T delta k k' ∧
                  TaggedOptionMapRel T U epsilon k u ∧
                    TaggedOptionMapRel T U epsilon k' u' ∧
                      hsame k BHist.Empty ∧ hsame k' BHist.Empty ∧
                        ((exists p q : BHist,
                          T p ∧ T q ∧ hsame k (BHist.e1 p) ∧
                            hsame k' (BHist.e1 q)) -> False) := by
  intro image sameMU sameM'U' sameUEmpty sameU'Empty
  have transported :
      TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon)
        u u' :=
    TaggedOptionPayloadDescentImageClassifier_hsame_transport
      (TaggedOptionDescentComp delta epsilon) certS source_hsame image sameMU sameM'U'
  cases transported with
  | intro h transported =>
      cases transported with
      | intro h' transported =>
          cases transported with
          | intro sourceClass maps =>
              cases maps with
              | intro compLeft compRight =>
                  have leftFactor :=
                    (TaggedOptionMapRel_composition_factorization_iff
                      delta epsilon rhoD rhoE epsilon_hsame).mp compLeft
                  have rightFactor :=
                    (TaggedOptionMapRel_composition_factorization_iff
                      delta epsilon rhoD rhoE epsilon_hsame).mp compRight
                  cases leftFactor with
                  | intro k leftData =>
                      cases rightFactor with
                      | intro k' rightData =>
                          have imageDelta :
                              TaggedOptionPayloadDescentImageClassifier S T delta k k' :=
                            Exists.intro h
                              (Exists.intro h'
                                (And.intro sourceClass
                                  (And.intro leftData.left rightData.left)))
                          have leftEmpty : hsame k BHist.Empty :=
                            Iff.mpr
                              (TaggedOptionMapRel_visible_branch_equivalence
                                epsilon leftData.right).left
                              sameUEmpty
                          have rightEmpty : hsame k' BHist.Empty :=
                            Iff.mpr
                              (TaggedOptionMapRel_visible_branch_equivalence
                                epsilon rightData.right).left
                              sameU'Empty
                          have noVisible :
                              (exists p q : BHist,
                                T p ∧ T q ∧ hsame k (BHist.e1 p) ∧
                                  hsame k' (BHist.e1 q)) -> False := by
                            intro visible
                            cases visible with
                            | intro p visible =>
                                cases visible with
                                | intro _q data =>
                                    exact not_hsame_emp_e1
                                      (hsame_trans (hsame_symm leftEmpty)
                                        data.right.right.left)
                          exact
                            ⟨k, k', imageDelta, leftData.right, rightData.right, leftEmpty,
                              rightEmpty, noVisible⟩

theorem TaggedOptionPayloadDescentImageClassifier_composite_normalized_absent_intermediate_constructor_exclusion
    {S T U : BHist -> Prop} {RelS RelT RelU : BHist -> BHist -> Prop}
    (delta : DescentCertificate BHist BHist RelS RelT)
    (epsilon : DescentCertificate BHist BHist RelT RelU)
    (rhoD : forall a : BHist, S a -> T (delta.map a))
    (rhoE : forall b : BHist, T b -> U (epsilon.map b))
    (epsilon_hsame :
      forall x y : BHist, T x -> T y -> hsame x y ->
        hsame (epsilon.map x) (epsilon.map y))
    (certS : NameCert S RelS)
    (source_hsame : TaggedOptionSourceHsameCompatible S RelS) {m m' u u' : BHist} :
    TaggedOptionPayloadDescentImageClassifier S U (TaggedOptionDescentComp delta epsilon) m m' ->
      hsame m u ->
        hsame m' u' ->
          hsame u BHist.Empty ->
            hsame u' BHist.Empty ->
              exists k k' : BHist,
                TaggedOptionPayloadDescentImageClassifier S T delta k k' ∧
                  TaggedOptionMapRel T U epsilon k u ∧
                    TaggedOptionMapRel T U epsilon k' u' ∧
                      hsame k BHist.Empty ∧ hsame k' BHist.Empty ∧
                        (forall t : BHist,
                          (hsame k (BHist.e0 t) -> False) ∧
                            (hsame k (BHist.e1 t) -> False)) ∧
                          (forall t : BHist,
                            (hsame k' (BHist.e0 t) -> False) ∧
                              (hsame k' (BHist.e1 t) -> False)) := by
  intro image sameMU sameM'U' sameUEmpty sameU'Empty
  have factorized :=
    TaggedOptionPayloadDescentImageClassifier_composite_normalized_absent_public_factorization
      delta epsilon rhoD rhoE epsilon_hsame certS source_hsame image sameMU sameM'U'
      sameUEmpty sameU'Empty
  cases factorized with
  | intro k factorized =>
      cases factorized with
      | intro k' data =>
          cases data with
          | intro imageDelta data =>
              cases data with
              | intro mapLeft data =>
                  cases data with
                  | intro mapRight data =>
                      cases data with
                      | intro sameKEmpty data =>
                          cases data with
                          | intro sameK'Empty _noVisible =>
                              have leftExclusion :
                                  forall t : BHist,
                                    (hsame k (BHist.e0 t) -> False) ∧
                                      (hsame k (BHist.e1 t) -> False) := by
                                intro t
                                constructor
                                · intro sameKE0
                                  exact not_hsame_emp_e0
                                    (hsame_trans (hsame_symm sameKEmpty) sameKE0)
                                · intro sameKE1
                                  exact not_hsame_emp_e1
                                    (hsame_trans (hsame_symm sameKEmpty) sameKE1)
                              have rightExclusion :
                                  forall t : BHist,
                                    (hsame k' (BHist.e0 t) -> False) ∧
                                      (hsame k' (BHist.e1 t) -> False) := by
                                intro t
                                constructor
                                · intro sameK'E0
                                  exact not_hsame_emp_e0
                                    (hsame_trans (hsame_symm sameK'Empty) sameK'E0)
                                · intro sameK'E1
                                  exact not_hsame_emp_e1
                                    (hsame_trans (hsame_symm sameK'Empty) sameK'E1)
                              exact
                                ⟨k, k', imageDelta, mapLeft, mapRight, sameKEmpty,
                                  sameK'Empty, leftExclusion, rightExclusion⟩

end BEDC.Derived.OptionUp
