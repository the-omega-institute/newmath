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

end BEDC.Derived.GroupUp
