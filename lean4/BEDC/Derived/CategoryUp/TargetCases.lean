import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_e1_target_morphism_cases {source r morph : BHist} :
    CategoryHomCarrier source (BHist.e1 r) morph ->
      (morph = BHist.Empty ∧ source = BHist.e1 r ∧ UnaryHistory r) ∨
        (∃ k : BHist,
          morph = BHist.e1 k ∧ UnaryHistory source ∧ UnaryHistory k ∧ Cont source k r) := by
  intro homCarrier
  cases homCarrier with
  | intro sourceCarrier rest =>
      cases rest with
      | intro targetCarrier rest =>
          cases rest with
          | intro morphCarrier homCont =>
              cases morph with
              | Empty =>
                  left
                  exact
                    And.intro rfl
                      (And.intro homCont.symm (unary_e1_inversion targetCarrier))
              | e0 k =>
                  exact False.elim (unary_no_zero_extension morphCarrier)
              | e1 k =>
                  right
                  exact
                    Exists.intro k
                      (And.intro rfl
                          (And.intro sourceCarrier
                            (And.intro (unary_e1_inversion morphCarrier)
                              (BHist.e1.inj homCont))))

theorem CategoryHomCarrier_e1_target_source_morphism_cases {source r morph : BHist} :
    CategoryHomCarrier source (BHist.e1 r) morph ->
      (source = BHist.Empty /\ morph = BHist.e1 r /\ UnaryHistory r) \/
        (exists a : BHist, source = BHist.e1 a /\ UnaryHistory a /\
          ((morph = BHist.Empty /\ hsame a r) \/
            (exists k : BHist, morph = BHist.e1 k /\ UnaryHistory k /\
              Cont (BHist.e1 a) k r))) := by
  intro homCarrier
  cases source with
  | Empty =>
      cases homCarrier with
      | intro _sourceCarrier rest =>
          cases rest with
          | intro targetCarrier rest =>
              cases rest with
              | intro _morphismCarrier homCont =>
                  cases morph with
                  | Empty =>
                      cases homCont
                  | e0 m =>
                      cases homCont
                  | e1 m =>
                      left
                      cases homCont
                      exact
                        And.intro rfl
                          (And.intro (congrArg BHist.e1 (append_empty_left m).symm)
                            (unary_e1_inversion targetCarrier))
  | e0 a =>
      exact False.elim (CategoryHomCarrier_e0_source_absurd homCarrier)
  | e1 a =>
      right
      have resultCases := CategoryHomCarrier_left_e1_result_cases homCarrier
      cases resultCases with
      | inl emptyCase =>
          exact
            Exists.intro a
              (And.intro rfl
                (And.intro emptyCase.right.left
                  (Or.inl (And.intro emptyCase.left emptyCase.right.right))))
      | inr visibleCase =>
          cases visibleCase with
          | intro k data =>
              exact
                Exists.intro a
                  (And.intro rfl
                    (And.intro (unary_e1_inversion homCarrier.left)
                      (Or.inr (Exists.intro k data))))

theorem CategoryHomCarrier_e1_morphism_target_cases {a target k : BHist} :
    CategoryHomCarrier a target (BHist.e1 k) ->
      ∃ r : BHist, target = BHist.e1 r ∧ CategoryHomCarrier a r k := by
  intro homCarrier
  cases homCarrier with
  | intro sourceCarrier rest =>
      cases rest with
      | intro targetCarrier rest =>
          cases rest with
          | intro morphCarrier homCont =>
              have targetWitness := cont_step_result_inversions.right homCont
              cases targetWitness with
              | intro r data =>
                  cases data with
                  | intro targetEq tailCont =>
                      cases targetEq
                      exact Exists.intro r
                        (And.intro rfl
                          (And.intro sourceCarrier
                            (And.intro (unary_e1_inversion targetCarrier)
                              (And.intro (unary_e1_inversion morphCarrier) tailCont))))

end BEDC.Derived.CategoryUp
