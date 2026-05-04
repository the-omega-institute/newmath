import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonClassifier_conjugation_action_determinacy {s x y : BHist} :
    GroupSingletonCarrier s -> GroupSingletonClassifier x y ->
      (let Conj := fun u z : BHist => append (append u z) BHist.Empty
      GroupSingletonClassifier (Conj s x) (Conj s y) ∧
        GroupSingletonClassifier (Conj BHist.Empty (Conj s x)) y) := by
  intro carrierS classified
  dsimp
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have sxInner : GroupSingletonCarrier (append s x) :=
    append_eq_empty_iff.mpr (And.intro carrierS classified.left)
  have syInner : GroupSingletonCarrier (append s y) :=
    append_eq_empty_iff.mpr (And.intro carrierS classified.right.left)
  have sxAction : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro sxInner emptyCarrier)
  have syAction : GroupSingletonCarrier (append (append s y) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro syInner emptyCarrier)
  have sameAction :
      hsame (append (append s x) BHist.Empty) (append (append s y) BHist.Empty) :=
    hsame_trans sxAction (hsame_symm syAction)
  have emptyThenSx : GroupSingletonCarrier
      (append BHist.Empty (append (append s x) BHist.Empty)) :=
    append_eq_empty_iff.mpr (And.intro emptyCarrier sxAction)
  have roundtripCarrier : GroupSingletonCarrier
      (append (append BHist.Empty (append (append s x) BHist.Empty)) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro emptyThenSx emptyCarrier)
  constructor
  · exact And.intro sxAction (And.intro syAction sameAction)
  · exact And.intro roundtripCarrier
      (And.intro classified.right.left
        (hsame_trans roundtripCarrier (hsame_symm classified.right.left)))

theorem GroupSingletonClassifier_normalizer_orbit_source_exact_iff {x y : BHist} :
    GroupSingletonCarrier x ->
      (let Conj := fun s z : BHist => append (append s z) BHist.Empty
      let Normalizer := fun s : BHist => GroupSingletonCarrier s
      let Orbit := fun p q : BHist =>
        Exists (fun s : BHist => Normalizer s ∧ GroupSingletonClassifier (Conj s p) q)
      Orbit x y <-> GroupSingletonClassifier x y) := by
  intro carrierX
  dsimp
  constructor
  · intro orbit
    cases orbit with
    | intro s witness =>
        have actionSplit := append_eq_empty_iff.mp witness.right.left
        have innerSplit := append_eq_empty_iff.mp actionSplit.left
        have sourceCarrier : GroupSingletonCarrier x := innerSplit.right
        have targetCarrier : GroupSingletonCarrier y := witness.right.right.left
        exact And.intro sourceCarrier
          (And.intro targetCarrier (hsame_trans sourceCarrier (hsame_symm targetCarrier)))
  · intro classified
    have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
    have emptyX : GroupSingletonCarrier (append BHist.Empty x) :=
      append_eq_empty_iff.mpr (And.intro emptyCarrier carrierX)
    have actionCarrier : GroupSingletonCarrier (append (append BHist.Empty x) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro emptyX emptyCarrier)
    exact Exists.intro BHist.Empty
      (And.intro emptyCarrier
        (And.intro actionCarrier
          (And.intro classified.right.left
            (hsame_trans actionCarrier (hsame_symm classified.right.left)))))

theorem GroupSingletonClassifier_append_conjugation_coverage_iff {s x y : BHist} :
    GroupSingletonCarrier s ->
      (GroupSingletonClassifier (append (append s x) BHist.Empty) y <->
        GroupSingletonCarrier x ∧ GroupSingletonCarrier y) := by
  intro carrierS
  constructor
  · intro classified
    have actionSplit := append_eq_empty_iff.mp classified.left
    have sourceSplit := append_eq_empty_iff.mp actionSplit.left
    exact And.intro sourceSplit.right classified.right.left
  · intro carriers
    have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
    have sourceCarrier : GroupSingletonCarrier (append s x) :=
      append_eq_empty_iff.mpr (And.intro carrierS carriers.left)
    have actionCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro sourceCarrier emptyCarrier)
    exact And.intro actionCarrier
      (And.intro carriers.right (hsame_trans actionCarrier (hsame_symm carriers.right)))

theorem GroupSingletonClassifier_conjugation_coverage_iff {s x y : BHist} :
    GroupSingletonCarrier s ->
      (let Conj := fun u z : BHist => append (append u z) BHist.Empty
       GroupSingletonClassifier (Conj s x) y <->
         GroupSingletonCarrier x ∧ GroupSingletonCarrier y) := by
  intro carrierS
  dsimp
  constructor
  · intro classified
    have actionSplit := append_eq_empty_iff.mp classified.left
    have innerSplit := append_eq_empty_iff.mp actionSplit.left
    exact And.intro innerSplit.right classified.right.left
  · intro carriers
    have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
    have innerCarrier : GroupSingletonCarrier (append s x) :=
      append_eq_empty_iff.mpr (And.intro carrierS carriers.left)
    have actionCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro innerCarrier emptyCarrier)
    exact And.intro actionCarrier
      (And.intro carriers.right (hsame_trans actionCarrier (hsame_symm carriers.right)))

theorem GroupSingletonNormalizerOrbit_total_coverage_iff {x y : BHist} :
    (let Conj := fun s z : BHist => append (append s z) BHist.Empty
     let Normalizer := fun s : BHist => GroupSingletonCarrier s
     let Orbit := fun p q : BHist =>
       Exists (fun s : BHist => Normalizer s ∧ GroupSingletonClassifier (Conj s p) q)
     Orbit x y <-> GroupSingletonCarrier x ∧ GroupSingletonCarrier y) := by
  dsimp
  constructor
  · intro orbit
    cases orbit with
    | intro s witness =>
        exact (GroupSingletonClassifier_conjugation_coverage_iff witness.left).mp witness.right
  · intro carriers
    have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
    have classified :
        GroupSingletonClassifier (append (append BHist.Empty x) BHist.Empty) y :=
      (GroupSingletonClassifier_conjugation_coverage_iff (s := BHist.Empty) emptyCarrier).mpr
        carriers
    exact Exists.intro BHist.Empty (And.intro emptyCarrier classified)

theorem GroupSingletonClassifier_normalizer_orbit_total_coverage_iff {x y : BHist} :
    ((Exists (fun s : BHist =>
        GroupSingletonCarrier s ∧
          GroupSingletonClassifier (append (append s x) BHist.Empty) y)) <->
      GroupSingletonCarrier x ∧ GroupSingletonCarrier y) := by
  constructor
  · intro orbit
    cases orbit with
    | intro s witness =>
        have actionSplit := append_eq_empty_iff.mp witness.right.left
        have innerSplit := append_eq_empty_iff.mp actionSplit.left
        exact And.intro innerSplit.right witness.right.right.left
  · intro carriers
    have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
    have emptyX : GroupSingletonCarrier (append BHist.Empty x) :=
      append_eq_empty_iff.mpr (And.intro emptyCarrier carriers.left)
    have actionCarrier : GroupSingletonCarrier (append (append BHist.Empty x) BHist.Empty) :=
      append_eq_empty_iff.mpr (And.intro emptyX emptyCarrier)
    exact Exists.intro BHist.Empty
      (And.intro emptyCarrier
        (And.intro actionCarrier
          (And.intro carriers.right
            (hsame_trans actionCarrier (hsame_symm carriers.right)))))

end BEDC.Derived.GroupUp
