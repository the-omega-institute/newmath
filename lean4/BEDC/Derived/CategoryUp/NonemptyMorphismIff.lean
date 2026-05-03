import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_source_nonempty_morphism_target_iff {a target morph : BHist} :
    (CategoryHomCarrier (BHist.e1 a) target morph /\
      (hsame morph BHist.Empty -> False)) <->
    (exists k r : BHist,
      morph = BHist.e1 k /\ target = BHist.e1 r /\ UnaryHistory a /\
        UnaryHistory k /\ UnaryHistory r /\ Cont (BHist.e1 a) k r) := by
  constructor
  · intro data
    exact CategoryHomCarrier_e1_source_nonempty_morphism_target_cases data.left data.right
  · intro witness
    cases witness with
    | intro k rest =>
        cases rest with
        | intro r data =>
            cases data with
            | intro morphEq rest =>
                cases rest with
                | intro targetEq rest =>
                    cases rest with
                    | intro sourceCarrier rest =>
                        cases rest with
                        | intro morphCarrier rest =>
                            cases rest with
                            | intro targetCarrier homCont =>
                                cases morphEq
                                cases targetEq
                                constructor
                                · exact And.intro (unary_e1_closed sourceCarrier)
                                    (And.intro (unary_e1_closed targetCarrier)
                                      (And.intro (unary_e1_closed morphCarrier)
                                        (cont_step_one homCont)))
                                · intro sameEmpty
                                  exact not_hsame_e1_empty sameEmpty

theorem CategoryHomCarrier_e1_target_nonempty_morphism_source_iff {source r morph : BHist} :
    (CategoryHomCarrier source (BHist.e1 r) morph /\
      (hsame morph BHist.Empty -> False)) <->
    ((source = BHist.Empty /\ morph = BHist.e1 r /\ UnaryHistory r) \/
      (exists a k : BHist,
        source = BHist.e1 a /\ morph = BHist.e1 k /\ UnaryHistory a /\
          UnaryHistory k /\ UnaryHistory r /\ Cont (BHist.e1 a) k r)) := by
  constructor
  · intro data
    exact CategoryHomCarrier_e1_target_nonempty_morphism_source_cases data.left data.right
  · intro splitData
    cases splitData with
    | inl emptySource =>
        cases emptySource with
        | intro sourceEq rest =>
            cases rest with
            | intro morphEq targetCarrier =>
                cases sourceEq
                cases morphEq
                constructor
                · exact (CategoryHomCarrier_empty_source_iff (b := BHist.e1 r)
                    (f := BHist.e1 r)).mpr
                    ⟨unary_e1_closed targetCarrier, hsame_refl (BHist.e1 r)⟩
                · intro sameEmpty
                  exact not_hsame_e1_empty sameEmpty
    | inr visibleSource =>
        cases visibleSource with
        | intro a rest =>
            cases rest with
            | intro k data =>
                cases data with
                | intro sourceEq rest =>
                    cases rest with
                    | intro morphEq rest =>
                        cases rest with
                        | intro sourceCarrier rest =>
                            cases rest with
                            | intro morphCarrier rest =>
                                cases rest with
                                | intro targetCarrier homCont =>
                                    cases sourceEq
                                    cases morphEq
                                    constructor
                                    · exact And.intro (unary_e1_closed sourceCarrier)
                                        (And.intro (unary_e1_closed targetCarrier)
                                          (And.intro (unary_e1_closed morphCarrier)
                                            (cont_step_one homCont)))
                                    · intro sameEmpty
                                      exact not_hsame_e1_empty sameEmpty

theorem CategoryHomCarrier_empty_source_nonempty_morphism_shape_iff {target morph : BHist} :
    (CategoryHomCarrier BHist.Empty target morph /\ (hsame morph BHist.Empty -> False)) <->
      exists r : BHist, target = BHist.e1 r /\ morph = BHist.e1 r /\ UnaryHistory r := by
  constructor
  · intro data
    have sourceData :=
      (CategoryHomCarrier_empty_source_iff (b := target) (f := morph)).mp data.left
    cases target with
    | Empty =>
        exact False.elim (data.right sourceData.right)
    | e0 t =>
        exact False.elim (unary_no_zero_extension sourceData.left)
    | e1 r =>
        cases sourceData.right
        exact Exists.intro r
          (And.intro rfl (And.intro rfl (unary_e1_inversion sourceData.left)))
  · intro witness
    cases witness with
    | intro r data =>
        cases data with
        | intro targetEq rest =>
            cases rest with
            | intro morphEq tailCarrier =>
                cases targetEq
                cases morphEq
                constructor
                · exact (CategoryHomCarrier_empty_source_iff (b := BHist.e1 r)
                    (f := BHist.e1 r)).mpr
                    (And.intro (unary_e1_closed tailCarrier) (hsame_refl (BHist.e1 r)))
                · intro sameEmpty
                  exact not_hsame_e1_empty sameEmpty

end BEDC.Derived.CategoryUp
