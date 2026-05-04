import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

def GroupSingletonNormalizerAction (s x : BHist) : BHist :=
  append (append s x) (GroupSingletonInv s)

def GroupSingletonNormalizerOrbit (x y : BHist) : Prop :=
  exists s : BHist,
    GroupSingletonCarrier s ∧
      GroupSingletonClassifier (append (append s x) (GroupSingletonInv s)) y

theorem GroupSingleton_normalizer_action_certificate {s x : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x ->
      let Conj := fun u y : BHist => append (append u y) BHist.Empty
      GroupSingletonCarrier (Conj s x) ∧
        GroupSingletonCarrier (Conj BHist.Empty x) ∧
          GroupSingletonClassifier (Conj s x) x ∧
            GroupSingletonClassifier (Conj BHist.Empty (Conj s x)) x := by
  intro carrierS carrierX
  cases carrierS
  cases carrierX
  dsimp
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · exact And.intro rfl (And.intro rfl rfl)
      · exact And.intro rfl (And.intro rfl rfl)

theorem GroupSingletonNormalizerAction_certificate {s x : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x ->
      let Conj : BHist -> BHist -> BHist := fun t y => append (append t y) BHist.Empty
      GroupSingletonCarrier (Conj s x) ∧ GroupSingletonCarrier (Conj BHist.Empty x) ∧
        GroupSingletonClassifier (Conj s x) x ∧
          GroupSingletonClassifier (Conj BHist.Empty (Conj s x)) x := by
  intro carrierS carrierX
  cases carrierS
  cases carrierX
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · exact hsame_refl BHist.Empty
    · constructor
      · exact And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
      · exact And.intro (hsame_refl BHist.Empty)
          (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

theorem GroupSingletonNormalizerOrbit_coverage_iff {x y : BHist} :
    (Exists (fun s : BHist => GroupSingletonCarrier s ∧
      GroupSingletonClassifier (append (append s x) BHist.Empty) y)) <->
        GroupSingletonCarrier x ∧ GroupSingletonCarrier y := by
  constructor
  · intro orbit
    cases orbit with
    | intro s witness =>
        have actionSplit := append_eq_empty_iff.mp witness.right.left
        have innerSplit := append_eq_empty_iff.mp actionSplit.left
        exact And.intro innerSplit.right witness.right.right.left
  · intro endpoints
    have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
    have emptyX : GroupSingletonCarrier (append BHist.Empty x) :=
      append_eq_empty_iff.mpr (And.intro emptyCarrier endpoints.left)
    have actionCarrier : GroupSingletonCarrier (append (append BHist.Empty x) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro emptyX emptyCarrier)
    exact Exists.intro BHist.Empty
      (And.intro emptyCarrier
        (And.intro actionCarrier
          (And.intro endpoints.right (hsame_trans actionCarrier (hsame_symm endpoints.right)))))

theorem GroupSingletonNormalizerOrbit_conjugator_pair_classifier_iff {s t x y : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier t ->
      (let Orbit := fun p q : BHist => Exists (fun u : BHist =>
        GroupSingletonCarrier u ∧
          GroupSingletonClassifier (append (append u p) BHist.Empty) q)
      Orbit (append (append s x) BHist.Empty) (append (append t y) BHist.Empty) <->
        GroupSingletonClassifier x y) := by
  intro carrierS carrierT
  constructor
  · intro orbit
    cases orbit with
    | intro u witness =>
        have actionCarrier := witness.right.left
        have targetCarrier := witness.right.right.left
        have actedSourceCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
          (append_eq_empty_iff.mp (append_eq_empty_iff.mp actionCarrier).left).right
        have sourceCarrier : GroupSingletonCarrier x :=
          (append_eq_empty_iff.mp (append_eq_empty_iff.mp actedSourceCarrier).left).right
        have targetBaseCarrier : GroupSingletonCarrier y :=
          (append_eq_empty_iff.mp (append_eq_empty_iff.mp targetCarrier).left).right
        exact And.intro sourceCarrier
          (And.intro targetBaseCarrier
            (hsame_trans sourceCarrier (hsame_symm targetBaseCarrier)))
  · intro classified
    have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
    have sourceProductCarrier : GroupSingletonCarrier (append s x) :=
      append_eq_empty_iff.mpr (And.intro carrierS classified.left)
    have actedSourceCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro sourceProductCarrier emptyCarrier)
    have orbitActionCarrier :
        GroupSingletonCarrier
          (append (append BHist.Empty (append (append s x) BHist.Empty)) BHist.Empty) :=
      append_eq_empty_iff.mpr
        (And.intro
          (append_eq_empty_iff.mpr (And.intro emptyCarrier actedSourceCarrier))
          emptyCarrier)
    have targetProductCarrier : GroupSingletonCarrier (append t y) :=
      append_eq_empty_iff.mpr (And.intro carrierT classified.right.left)
    have targetCarrier : GroupSingletonCarrier (append (append t y) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro targetProductCarrier emptyCarrier)
    exact Exists.intro BHist.Empty
      (And.intro emptyCarrier
        (And.intro orbitActionCarrier
          (And.intro targetCarrier
            (hsame_trans orbitActionCarrier (hsame_symm targetCarrier)))))

theorem GroupSingletonNormalizerOrbit_visible_source_absurd {p y : BHist} :
    ((Exists (fun s : BHist =>
        GroupSingletonCarrier s ∧
          GroupSingletonClassifier (append (append s (BHist.e0 p)) BHist.Empty) y)) ->
      False) ∧
      ((Exists (fun s : BHist =>
        GroupSingletonCarrier s ∧
          GroupSingletonClassifier (append (append s (BHist.e1 p)) BHist.Empty) y)) ->
      False) := by
  constructor
  · intro orbit
    cases orbit with
    | intro s witness =>
        have actionSplit := append_eq_empty_iff.mp witness.right.left
        have sourceSplit := append_eq_empty_iff.mp actionSplit.left
        exact not_hsame_e0_empty sourceSplit.right
  · intro orbit
    cases orbit with
    | intro s witness =>
        have actionSplit := append_eq_empty_iff.mp witness.right.left
        have sourceSplit := append_eq_empty_iff.mp actionSplit.left
        exact not_hsame_e1_empty sourceSplit.right

theorem GroupSingletonNormalizerOrbit_action_single_fiber_iff {s x y : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x ->
      (GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty) y <->
        GroupSingletonCarrier y) := by
  intro carrierS carrierX
  have actionCertificate := GroupSingleton_normalizer_action_certificate carrierS carrierX
  have actionCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
    actionCertificate.left
  constructor
  · intro orbit
    exact (GroupSingletonNormalizerOrbit_coverage_iff.mp orbit).right
  · intro carrierY
    exact GroupSingletonNormalizerOrbit_coverage_iff.mpr
      (And.intro actionCarrier carrierY)

theorem GroupSingletonNormalizerOrbit_action_identity_iff {s x y : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x -> GroupSingletonCarrier y ->
      (GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty) y <->
        GroupSingletonNormalizerOrbit x y) := by
  intro carrierS carrierX carrierY
  constructor
  · intro _actedOrbit
    exact GroupSingletonNormalizerOrbit_coverage_iff.mpr (And.intro carrierX carrierY)
  · intro _sourceOrbit
    exact (GroupSingletonNormalizerOrbit_action_single_fiber_iff carrierS carrierX).mpr carrierY

theorem GroupSingletonNormalizerOrbit_action_invariance {s x y : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x -> GroupSingletonCarrier y ->
      GroupSingletonNormalizerOrbit x y ->
        GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
          (append (append s y) BHist.Empty) := by
  intro carrierS _carrierX _carrierY orbit
  have endpoints := GroupSingletonNormalizerOrbit_coverage_iff.mp orbit
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have actionXCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro carrierS endpoints.left)) emptyCarrier)
  have actionYCarrier : GroupSingletonCarrier (append (append s y) BHist.Empty) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro carrierS endpoints.right)) emptyCarrier)
  exact GroupSingletonNormalizerOrbit_coverage_iff.mpr
    (And.intro actionXCarrier actionYCarrier)

theorem GroupSingletonNormalizerOrbit_two_conjugator_coverage_iff {s t x y : BHist} :
    GroupSingletonCarrier s → GroupSingletonCarrier t →
      ((Exists (fun u : BHist => GroupSingletonCarrier u ∧
        GroupSingletonClassifier
          (append (append u (append (append s x) BHist.Empty)) BHist.Empty)
          (append (append t y) BHist.Empty))) ↔
          GroupSingletonCarrier x ∧ GroupSingletonCarrier y) := by
  intro carrierS carrierT
  constructor
  · intro orbit
    cases orbit with
    | intro u witness =>
        have actedSourceCarrier :
            GroupSingletonCarrier
              (append (append u (append (append s x) BHist.Empty)) BHist.Empty) :=
          witness.right.left
        have actedTargetCarrier :
            GroupSingletonCarrier (append (append t y) BHist.Empty) :=
          witness.right.right.left
        have outerSource := append_eq_empty_iff.mp actedSourceCarrier
        have middleSource := append_eq_empty_iff.mp outerSource.left
        have sxEndpoint := append_eq_empty_iff.mp middleSource.right
        have sxProduct := append_eq_empty_iff.mp sxEndpoint.left
        have targetEndpoint := append_eq_empty_iff.mp actedTargetCarrier
        have targetProduct := append_eq_empty_iff.mp targetEndpoint.left
        exact And.intro sxProduct.right targetProduct.right
  · intro endpoints
    have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
    have sourceProductCarrier : GroupSingletonCarrier (append s x) :=
      append_eq_empty_iff.mpr (And.intro carrierS endpoints.left)
    have sourceActionCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro sourceProductCarrier emptyCarrier)
    have sourceMiddleCarrier :
        GroupSingletonCarrier (append BHist.Empty (append (append s x) BHist.Empty)) :=
      append_eq_empty_iff.mpr (And.intro emptyCarrier sourceActionCarrier)
    have sourceCarrier :
        GroupSingletonCarrier
          (append (append BHist.Empty (append (append s x) BHist.Empty)) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro sourceMiddleCarrier emptyCarrier)
    have targetProductCarrier : GroupSingletonCarrier (append t y) :=
      append_eq_empty_iff.mpr (And.intro carrierT endpoints.right)
    have targetCarrier : GroupSingletonCarrier (append (append t y) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro targetProductCarrier emptyCarrier)
    exact Exists.intro BHist.Empty
      (And.intro emptyCarrier
        (And.intro sourceCarrier
          (And.intro targetCarrier (hsame_trans sourceCarrier (hsame_symm targetCarrier)))))

theorem GroupSingletonNormalizerOrbit_two_conjugator_classifier_iff {s t x y : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier t ->
      ((Exists (fun u : BHist => GroupSingletonCarrier u ∧
        GroupSingletonClassifier
          (append (append u (append (append s x) BHist.Empty)) BHist.Empty)
          (append (append t y) BHist.Empty))) <-> GroupSingletonClassifier x y) := by
  intro carrierS carrierT
  constructor
  · intro orbit
    cases orbit with
    | intro u witness =>
        have leftOuter := append_eq_empty_iff.mp witness.right.left
        have leftInner := append_eq_empty_iff.mp leftOuter.left
        have sourceActionSplit := append_eq_empty_iff.mp leftInner.right
        have sourceSplit := append_eq_empty_iff.mp sourceActionSplit.left
        have rightOuter := append_eq_empty_iff.mp witness.right.right.left
        have targetSplit := append_eq_empty_iff.mp rightOuter.left
        exact And.intro sourceSplit.right
          (And.intro targetSplit.right
            (hsame_trans sourceSplit.right (hsame_symm targetSplit.right)))
  · intro classified
    have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
    have sourceProduct : GroupSingletonCarrier (append s x) :=
      append_eq_empty_iff.mpr (And.intro carrierS classified.left)
    have sourceAction : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro sourceProduct emptyCarrier)
    have witnessProduct :
        GroupSingletonCarrier (append BHist.Empty (append (append s x) BHist.Empty)) :=
      append_eq_empty_iff.mpr (And.intro emptyCarrier sourceAction)
    have witnessAction :
        GroupSingletonCarrier
          (append (append BHist.Empty (append (append s x) BHist.Empty)) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro witnessProduct emptyCarrier)
    have targetProduct : GroupSingletonCarrier (append t y) :=
      append_eq_empty_iff.mpr (And.intro carrierT classified.right.left)
    have targetAction : GroupSingletonCarrier (append (append t y) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro targetProduct emptyCarrier)
    exact Exists.intro BHist.Empty
      (And.intro emptyCarrier
        (And.intro witnessAction
          (And.intro targetAction (hsame_trans witnessAction (hsame_symm targetAction)))))

theorem GroupSingletonNormalizerAction_composition_collapse {s t x : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier t -> GroupSingletonCarrier x ->
      GroupSingletonCarrier (append (append t x) BHist.Empty) ∧
      GroupSingletonCarrier
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty) ∧
      GroupSingletonCarrier (append (append (append s t) x) BHist.Empty) ∧
      GroupSingletonClassifier
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty) x ∧
      GroupSingletonClassifier (append (append (append s t) x) BHist.Empty) x := by
  intro carrierS carrierT carrierX
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have txCarrier : GroupSingletonCarrier (append t x) :=
    append_eq_empty_iff.mpr (And.intro carrierT carrierX)
  have actionTCarrier : GroupSingletonCarrier (append (append t x) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro txCarrier emptyCarrier)
  have nestedCarrier :
      GroupSingletonCarrier
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty) :=
    append_eq_empty_iff.mpr
      (And.intro
        (append_eq_empty_iff.mpr (And.intro carrierS actionTCarrier))
        emptyCarrier)
  have stCarrier : GroupSingletonCarrier (append s t) :=
    append_eq_empty_iff.mpr (And.intro carrierS carrierT)
  have stxCarrier : GroupSingletonCarrier (append (append s t) x) :=
    append_eq_empty_iff.mpr (And.intro stCarrier carrierX)
  have composedCarrier : GroupSingletonCarrier (append (append (append s t) x) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro stxCarrier emptyCarrier)
  exact And.intro actionTCarrier
    (And.intro nestedCarrier
      (And.intro composedCarrier
          (And.intro
            (And.intro nestedCarrier
              (And.intro carrierX (hsame_trans nestedCarrier (hsame_symm carrierX))))
          (And.intro composedCarrier
            (And.intro carrierX (hsame_trans composedCarrier (hsame_symm carrierX)))))))

theorem GroupSingletonNormalizerAction_product_coherent_orbit_collapse {s t x : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier t -> GroupSingletonCarrier x ->
      GroupSingletonClassifier
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty)
        (append (append (append s t) x) BHist.Empty) ∧
      GroupSingletonClassifier
        (append (append (append s t) x) BHist.Empty)
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty) := by
  intro carrierS carrierT carrierX
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have txCarrier : GroupSingletonCarrier (append t x) :=
    append_eq_empty_iff.mpr (And.intro carrierT carrierX)
  have actionTCarrier : GroupSingletonCarrier (append (append t x) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro txCarrier emptyCarrier)
  have nestedInnerCarrier :
      GroupSingletonCarrier (append s (append (append t x) BHist.Empty)) :=
    append_eq_empty_iff.mpr (And.intro carrierS actionTCarrier)
  have nestedCarrier :
      GroupSingletonCarrier
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro nestedInnerCarrier emptyCarrier)
  have stCarrier : GroupSingletonCarrier (append s t) :=
    append_eq_empty_iff.mpr (And.intro carrierS carrierT)
  have stxCarrier : GroupSingletonCarrier (append (append s t) x) :=
    append_eq_empty_iff.mpr (And.intro stCarrier carrierX)
  have composedCarrier : GroupSingletonCarrier (append (append (append s t) x) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro stxCarrier emptyCarrier)
  constructor
  · exact And.intro nestedCarrier
      (And.intro composedCarrier (hsame_trans nestedCarrier (hsame_symm composedCarrier)))
  · exact And.intro composedCarrier
      (And.intro nestedCarrier (hsame_trans composedCarrier (hsame_symm nestedCarrier)))

theorem GroupSingletonNormalizerOrbit_product_coherent_action_law {s t x : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier t -> GroupSingletonCarrier x ->
      GroupSingletonNormalizerOrbit
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty)
        (append (append (append s t) x) BHist.Empty) ∧
      GroupSingletonNormalizerOrbit
        (append (append (append s t) x) BHist.Empty)
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty) := by
  intro carrierS carrierT carrierX
  have collapse :=
    GroupSingletonNormalizerAction_product_coherent_orbit_collapse carrierS carrierT carrierX
  have nestedSource :
      GroupSingletonCarrier
        (append (append s (append (append t x) BHist.Empty)) BHist.Empty) :=
    collapse.left.left
  have composedSource :
      GroupSingletonCarrier (append (append (append s t) x) BHist.Empty) :=
    collapse.left.right.left
  constructor
  · exact GroupSingletonNormalizerOrbit_coverage_iff.mpr
      (And.intro nestedSource composedSource)
  · exact GroupSingletonNormalizerOrbit_coverage_iff.mpr
      (And.intro composedSource nestedSource)

theorem GroupSingletonNormalizerOrbit_action_law_package {s t x y : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier t -> GroupSingletonCarrier x ->
      GroupSingletonCarrier y -> GroupSingletonNormalizerOrbit x y ->
        GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
            (append (append s y) BHist.Empty) ∧
          GroupSingletonNormalizerOrbit
            (append (append BHist.Empty (append (append s x) BHist.Empty)) BHist.Empty) y ∧
            GroupSingletonNormalizerOrbit
              (append (append s (append (append t x) BHist.Empty)) BHist.Empty)
              (append (append (append s t) x) BHist.Empty) := by
  intro carrierS carrierT carrierX carrierY orbit
  have invariant :
      GroupSingletonNormalizerOrbit (append (append s x) BHist.Empty)
        (append (append s y) BHist.Empty) :=
    GroupSingletonNormalizerOrbit_action_invariance carrierS carrierX carrierY orbit
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have sourceProductCarrier : GroupSingletonCarrier (append s x) :=
    append_eq_empty_iff.mpr (And.intro carrierS carrierX)
  have sourceActionCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro sourceProductCarrier emptyCarrier)
  have roundtripProductCarrier :
      GroupSingletonCarrier (append BHist.Empty (append (append s x) BHist.Empty)) :=
    append_eq_empty_iff.mpr (And.intro emptyCarrier sourceActionCarrier)
  have roundtripCarrier :
      GroupSingletonCarrier
        (append (append BHist.Empty (append (append s x) BHist.Empty)) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro roundtripProductCarrier emptyCarrier)
  have roundtripOrbit :
      GroupSingletonNormalizerOrbit
        (append (append BHist.Empty (append (append s x) BHist.Empty)) BHist.Empty) y :=
    GroupSingletonNormalizerOrbit_coverage_iff.mpr
      (And.intro roundtripCarrier carrierY)
  have productLaw :=
    (GroupSingletonNormalizerOrbit_product_coherent_action_law carrierS carrierT carrierX).left
  exact And.intro invariant (And.intro roundtripOrbit productLaw)

end BEDC.Derived.GroupUp
