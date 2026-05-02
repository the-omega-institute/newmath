import BEDC.Derived.CategoryUp

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem CategoryHomCarrier_empty_source_e1_target_iff {r morph : BHist} :
    CategoryHomCarrier BHist.Empty (BHist.e1 r) morph <->
      morph = BHist.e1 r /\ UnaryHistory r := by
  constructor
  · intro homCarrier
    have data :=
      (CategoryHomCarrier_empty_source_iff (b := BHist.e1 r) (f := morph)).mp homCarrier
    exact And.intro data.right (unary_e1_inversion data.left)
  · intro data
    exact
      (CategoryHomCarrier_empty_source_iff (b := BHist.e1 r) (f := morph)).mpr
        (And.intro (unary_e1_closed data.right) data.left)

theorem CategoryHomCarrier_empty_source_e1_morphism_iff {k target : BHist} :
    CategoryHomCarrier BHist.Empty target (BHist.e1 k) <->
      target = BHist.e1 k /\ UnaryHistory k := by
  constructor
  · intro homCarrier
    have data :=
      (CategoryHomCarrier_empty_source_iff (b := target) (f := BHist.e1 k)).mp homCarrier
    cases data.right
    exact And.intro rfl (unary_e1_inversion data.left)
  · intro data
    have targetCarrier : UnaryHistory target := by
      cases data.left
      exact unary_e1_closed data.right
    exact
      (CategoryHomCarrier_empty_source_iff (b := target) (f := BHist.e1 k)).mpr
        (And.intro targetCarrier data.left.symm)

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

theorem CategoryHomCarrier_e1_morphism_source_target_cases {source target k : BHist} :
    CategoryHomCarrier source target (BHist.e1 k) ->
      (source = BHist.Empty /\ target = BHist.e1 k /\ UnaryHistory k) \/
        (exists a r : BHist, source = BHist.e1 a /\ target = BHist.e1 r /\
          UnaryHistory a /\ UnaryHistory k /\ UnaryHistory r /\ Cont (BHist.e1 a) k r) := by
  intro homCarrier
  cases source with
  | Empty =>
      have emptyData :=
        (CategoryHomCarrier_empty_source_e1_morphism_iff (k := k) (target := target)).mp
          homCarrier
      left
      exact And.intro rfl (And.intro emptyData.left emptyData.right)
  | e0 a =>
      exact False.elim (CategoryHomCarrier_e0_source_absurd homCarrier)
  | e1 a =>
      have targetData :=
        (CategoryHomCarrier_e1_source_e1_morphism_target_iff (a := a) (k := k)
          (target := target)).mp homCarrier
      cases targetData with
      | intro r data =>
          right
          exact Exists.intro a
            (Exists.intro r
              (And.intro rfl data))

theorem CategoryHomCarrier_e1_source_e1_target_morphism_iff {a r morph : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) morph ↔
      (morph = BHist.Empty ∧ UnaryHistory a ∧ hsame a r) ∨
        (∃ k : BHist, morph = BHist.e1 k ∧ UnaryHistory a ∧ UnaryHistory k ∧
          Cont (BHist.e1 a) k r) := by
  constructor
  · intro homCarrier
    have sourceCarrier : UnaryHistory a := unary_e1_inversion homCarrier.left
    have splitCases := CategoryHomCarrier_left_e1_result_cases homCarrier
    cases splitCases with
    | inl emptyCase =>
        left
        exact emptyCase
    | inr visibleCase =>
        right
        cases visibleCase with
        | intro k data =>
            cases data with
            | intro morphEq rest =>
                cases rest with
                | intro morphCarrier homCont =>
                    exact Exists.intro k
                      (And.intro morphEq
                        (And.intro sourceCarrier (And.intro morphCarrier homCont)))
  · intro splitCases
    cases splitCases with
    | inl emptyCase =>
        cases emptyCase with
        | intro morphEq rest =>
            cases rest with
            | intro sourceCarrier sameTarget =>
                cases morphEq
                cases sameTarget
                exact And.intro (unary_e1_closed sourceCarrier)
                  (And.intro (unary_e1_closed sourceCarrier)
                    (And.intro unary_empty (cont_right_unit (BHist.e1 a))))
    | inr visibleCase =>
        cases visibleCase with
        | intro k data =>
            cases data with
            | intro morphEq rest =>
                cases rest with
                | intro sourceCarrier rest =>
                    cases rest with
                    | intro morphCarrier homCont =>
                        cases morphEq
                        exact And.intro (unary_e1_closed sourceCarrier)
                          (And.intro
                            (unary_e1_closed
                              (unary_cont_closed (unary_e1_closed sourceCarrier)
                                morphCarrier homCont))
                            (And.intro (unary_e1_closed morphCarrier)
                              (cont_step_one homCont)))

theorem CategoryHomCarrier_e1_source_e1_target_morphism_alignment {a r m n : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) m ->
      CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) n ->
        (m = BHist.Empty ∧ n = BHist.Empty) ∨
          (∃ k l : BHist, m = BHist.e1 k ∧ n = BHist.e1 l ∧ hsame k l) := by
  intro left right
  have sameMorphism : hsame m n := CategoryHomCarrier_morphism_deterministic left right
  have splitLeft := CategoryHomCarrier_left_e1_result_cases left
  cases splitLeft with
  | inl emptyCase =>
      cases emptyCase with
      | intro mEmpty _rest =>
          cases mEmpty
          cases sameMorphism
          exact Or.inl (And.intro rfl rfl)
  | inr visibleCase =>
      cases visibleCase with
      | intro k data =>
          cases data with
          | intro mEq _rest =>
              cases mEq
              cases n with
              | Empty =>
                  cases sameMorphism
              | e0 l =>
                  cases sameMorphism
              | e1 l =>
                  exact Or.inr
                    (Exists.intro k
                      (Exists.intro l
                        (And.intro rfl (And.intro rfl (BHist.e1.inj sameMorphism)))))

theorem CategoryHomCarrier_e1_source_e1_target_nonempty_morphism_alignment {a r m n : BHist} :
    CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) m ->
      CategoryHomCarrier (BHist.e1 a) (BHist.e1 r) n ->
        (hsame m BHist.Empty -> False) ->
          exists k : BHist, exists l : BHist, m = BHist.e1 k /\ n = BHist.e1 l /\
            hsame k l := by
  intro left right nonempty
  have alignment := CategoryHomCarrier_e1_source_e1_target_morphism_alignment left right
  cases alignment with
  | inl emptyCase =>
      exact False.elim (nonempty (by cases emptyCase.left; exact hsame_refl BHist.Empty))
  | inr visibleCase =>
      exact visibleCase

theorem CategoryHomCarrier_comp_e1_morphism_target_factor {a b c f g k : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g (BHist.e1 k) ->
      ∃ r : BHist, c = BHist.e1 r ∧ CategoryHomCarrier a r k ∧
        CategoryHomCarrier b (BHist.e1 r) g := by
  intro left right comp
  have composite : CategoryHomCarrier a c (BHist.e1 k) :=
    CategoryHomCarrier_comp_closed left right comp
  have targetCases := CategoryHomCarrier_e1_morphism_target_cases composite
  cases targetCases with
  | intro r targetData =>
      cases targetData with
      | intro targetEq tailCarrier =>
          cases targetEq
          exact Exists.intro r (And.intro rfl (And.intro tailCarrier right))

theorem CategoryHomCarrier_comp_e1_morphism_right_factor_cases {a b c f g k : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g (BHist.e1 k) ->
      (g = BHist.Empty ∧ c = b ∧ CategoryHomCarrier a b (BHist.e1 k)) ∨
        (∃ l r : BHist, g = BHist.e1 l ∧ c = BHist.e1 r ∧
          CategoryHomCarrier a r k ∧ CategoryHomCarrier b (BHist.e1 r) (BHist.e1 l)) := by
  intro left right comp
  have targetFactor :=
    CategoryHomCarrier_comp_e1_morphism_target_factor left right comp
  cases targetFactor with
  | intro r factorData =>
      cases factorData with
      | intro targetEq rest =>
          cases rest with
          | intro tailCarrier rightFactor =>
              cases targetEq
              have rightCases := CategoryHomCarrier_e1_target_morphism_cases rightFactor
              cases rightCases with
              | inl emptyCase =>
                  cases emptyCase with
                  | intro morphEq rest =>
                      cases rest with
                      | intro sourceEq _targetCarrier =>
                          left
                          exact And.intro morphEq
                            (And.intro sourceEq.symm
                              (by
                                cases sourceEq
                                exact
                                  (CategoryHomCarrier_e1_morphism_target_iff).mpr
                                    (And.intro tailCarrier.left
                                      (And.intro tailCarrier.right.right.left
                                        tailCarrier.right.right.right))))
              | inr visibleCase =>
                  cases visibleCase with
                  | intro l data =>
                      cases data with
                      | intro morphEq _rest =>
                          right
                          exact Exists.intro l
                            (Exists.intro r
                              (And.intro morphEq
                                (And.intro rfl
                                  (And.intro tailCarrier
                                    (by
                                      cases morphEq
                                      exact rightFactor)))))

theorem CategoryHomCarrier_comp_e1_morphism_left_factor_cases {a b c f g k : BHist} :
    CategoryHomCarrier a b f -> CategoryHomCarrier b c g -> Cont f g (BHist.e1 k) ->
      (f = BHist.Empty ∧ a = b ∧ CategoryHomCarrier b c (BHist.e1 k)) ∨
        (∃ l r : BHist, f = BHist.e1 l ∧ b = BHist.e1 r ∧
          CategoryHomCarrier a r l ∧ CategoryHomCarrier (BHist.e1 r) c g ∧
            Cont (BHist.e1 l) g (BHist.e1 k)) := by
  intro left right comp
  cases f with
  | Empty =>
      left
      have sameMorphism : hsame g (BHist.e1 k) := hsame_symm (cont_left_unit_result comp)
      exact And.intro rfl
        (And.intro left.right.right.right.symm
          (CategoryHomCarrier_hsame_transport (hsame_refl b) (hsame_refl c) sameMorphism
            right))
  | e0 l =>
      exact False.elim (unary_no_zero_extension left.right.right.left)
  | e1 l =>
      right
      have targetCases := CategoryHomCarrier_e1_morphism_target_cases left
      cases targetCases with
      | intro r targetData =>
          cases targetData with
          | intro targetEq tailCarrier =>
              exact Exists.intro l
                (Exists.intro r
                  (And.intro rfl
                    (And.intro targetEq
                      (And.intro tailCarrier
                        (And.intro
                          (by
                            cases targetEq
                            exact right)
                          comp)))))

theorem CategoryHomCarrier_visible_composable_morphisms_target_cases {a b c l m k : BHist} :
    CategoryHomCarrier a b (BHist.e1 l) -> CategoryHomCarrier b c (BHist.e1 m) ->
      Cont (BHist.e1 l) (BHist.e1 m) (BHist.e1 k) ->
        ∃ r s : BHist, b = BHist.e1 r ∧ c = BHist.e1 s ∧
          CategoryHomCarrier a r l ∧ CategoryHomCarrier (BHist.e1 r) s m ∧
            Cont (BHist.e1 l) (BHist.e1 m) (BHist.e1 k) := by
  intro left right comp
  have leftCases := CategoryHomCarrier_e1_morphism_target_cases left
  have rightCases := CategoryHomCarrier_e1_morphism_target_cases right
  cases leftCases with
  | intro r leftData =>
      cases rightCases with
      | intro s rightData =>
          cases leftData with
          | intro bEq leftTail =>
              cases rightData with
              | intro cEq rightTail =>
                  cases bEq
                  exact Exists.intro r
                    (Exists.intro s
                      (And.intro rfl
                        (And.intro cEq (And.intro leftTail (And.intro rightTail comp)))))

theorem CategoryHomCarrier_comp_visible_morphisms_result_cases {a b c l m fg : BHist} :
    CategoryHomCarrier a b (BHist.e1 l) -> CategoryHomCarrier b c (BHist.e1 m) ->
      Cont (BHist.e1 l) (BHist.e1 m) fg ->
        ∃ k : BHist, fg = BHist.e1 k ∧ Cont (BHist.e1 l) m k ∧
          CategoryHomCarrier a c (BHist.e1 k) := by
  intro left right comp
  cases comp
  exact Exists.intro (append (BHist.e1 l) m)
    (And.intro rfl
      (And.intro (cont_intro rfl)
        (CategoryHomCarrier_comp_closed left right (cont_intro rfl))))

end BEDC.Derived.CategoryUp
