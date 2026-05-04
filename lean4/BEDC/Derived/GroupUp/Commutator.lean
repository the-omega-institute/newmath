import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem GroupSingletonCommutator_terminal_collapse {x y : BHist} :
    GroupSingletonCarrier x -> GroupSingletonCarrier y ->
      GroupSingletonCarrier (append (append (append x y) BHist.Empty) BHist.Empty) ∧
        GroupSingletonClassifier (append (append (append x y) BHist.Empty) BHist.Empty)
          BHist.Empty := by
  intro carrierX carrierY
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have productCarrier : GroupSingletonCarrier (append x y) :=
    append_eq_empty_iff.mpr (And.intro carrierX carrierY)
  have inverseXCarrier : GroupSingletonCarrier (append (append x y) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro productCarrier emptyCarrier)
  have commutatorCarrier :
      GroupSingletonCarrier (append (append (append x y) BHist.Empty) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro inverseXCarrier emptyCarrier)
  exact And.intro commutatorCarrier
    (And.intro commutatorCarrier (And.intro emptyCarrier commutatorCarrier))

theorem group_commutator_trivial_iff_commutes_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (leftId : forall x : BHist, hsame (mul BHist.Empty x) x)
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b : BHist} :
    hsame (mul (mul a b) (mul (inv a) (inv b))) BHist.Empty <->
      hsame (mul a b) (mul b a) := by
  have reverseBA :
      hsame (inv (mul b a)) (mul (inv a) (inv b)) := by
    exact group_inverse_mul_reverse assocC leftId rightId mulCongr leftInv rightInv b a
  constructor
  · intro commUnit
    have reverseLeftInverse :
        hsame (mul (mul (inv a) (inv b)) (mul b a)) BHist.Empty := by
      exact hsame_trans
        (mulCongr (hsame_symm reverseBA) (hsame_refl (mul b a)))
        (leftInv (mul b a))
    exact group_left_right_inverse_uniqueness
      assocC leftId rightId mulCongr commUnit reverseLeftInverse
  · intro commute
    exact hsame_trans
      (mulCongr commute (hsame_symm reverseBA))
      (rightInv (mul b a))

protected theorem group_conjugation_fixed_point_commutation_iff_from_empty_unit
    {mul : BHist -> BHist -> BHist} {inv : BHist -> BHist}
    (assocC : forall x y z : BHist, hsame (mul (mul x y) z) (mul x (mul y z)))
    (rightId : forall x : BHist, hsame (mul x BHist.Empty) x)
    (mulCongr : forall {a a' b b' : BHist}, hsame a a' -> hsame b b' ->
      hsame (mul a b) (mul a' b'))
    (leftInv : forall x : BHist, hsame (mul (inv x) x) BHist.Empty)
    (rightInv : forall x : BHist, hsame (mul x (inv x)) BHist.Empty)
    {a b : BHist} :
    hsame (mul (mul a b) (inv a)) b <-> hsame (mul a b) (mul b a) := by
  constructor
  · intro fixed
    have transported :
        hsame (mul (mul (mul a b) (inv a)) a) (mul b a) := by
      exact mulCongr fixed (hsame_refl a)
    have collapse :
        hsame (mul (mul (mul a b) (inv a)) a) (mul a b) := by
      exact hsame_trans (assocC (mul a b) (inv a) a)
        (hsame_trans (mulCongr (hsame_refl (mul a b)) (leftInv a))
          (rightId (mul a b)))
    exact hsame_trans (hsame_symm collapse) transported
  · intro commute
    have transported : hsame (mul (mul a b) (inv a)) (mul (mul b a) (inv a)) := by
      exact mulCongr commute (hsame_refl (inv a))
    have collapse : hsame (mul (mul b a) (inv a)) b := by
      exact hsame_trans (assocC b a (inv a))
        (hsame_trans (mulCongr (hsame_refl b) (rightInv a)) (rightId b))
    exact hsame_trans transported collapse

theorem GroupSingletonClassifier_commutator_terminal_collapse {x y : BHist} :
    GroupSingletonCarrier x -> GroupSingletonCarrier y ->
      GroupSingletonCarrier (append (append (append x y) BHist.Empty) BHist.Empty) ∧
        GroupSingletonClassifier
          (append (append (append x y) BHist.Empty) BHist.Empty) BHist.Empty := by
  intro carrierX carrierY
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have productCarrier : GroupSingletonCarrier (append x y) :=
    append_eq_empty_iff.mpr (And.intro carrierX carrierY)
  have inverseTailCarrier : GroupSingletonCarrier (append (append x y) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro productCarrier emptyCarrier)
  have commutatorCarrier :
      GroupSingletonCarrier (append (append (append x y) BHist.Empty) BHist.Empty) :=
    append_eq_empty_iff.mpr (And.intro inverseTailCarrier emptyCarrier)
  exact And.intro commutatorCarrier
    (And.intro commutatorCarrier
      (And.intro emptyCarrier (hsame_trans commutatorCarrier (hsame_symm emptyCarrier))))

theorem GroupSingletonClassifier_commutator_unit_exactness_iff {x y : BHist} :
    GroupSingletonClassifier (append (append (append x y) BHist.Empty) BHist.Empty)
        BHist.Empty <->
      GroupSingletonCarrier x ∧ GroupSingletonCarrier y := by
  constructor
  · intro classified
    have outerSplit := append_eq_empty_iff.mp classified.left
    have inverseTailSplit := append_eq_empty_iff.mp outerSplit.left
    exact append_eq_empty_iff.mp inverseTailSplit.left
  · intro carriers
    exact (GroupSingletonClassifier_commutator_terminal_collapse carriers.left carriers.right).right

theorem GroupSingletonCommutator_conjugated_invariance {s x y : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x -> GroupSingletonCarrier y ->
      (let Conj : BHist -> BHist := fun z => append (append s z) BHist.Empty;
       let Comm : BHist -> BHist -> BHist := fun a b =>
        append (append (append a b) BHist.Empty) BHist.Empty;
       GroupSingletonClassifier (Comm (Conj x) (Conj y)) (Comm x y) ∧
        GroupSingletonClassifier (Comm (Conj x) (Conj y)) BHist.Empty ∧
          GroupSingletonClassifier (Comm x y) BHist.Empty) := by
  intro carrierS carrierX carrierY
  cases carrierS; cases carrierX; cases carrierY
  exact ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

theorem GroupSingletonClassifier_append_commutator_terminal_exactness_iff {x y : BHist} :
    (GroupSingletonCarrier (append (append (append x y) BHist.Empty) BHist.Empty) <->
      GroupSingletonCarrier x ∧ GroupSingletonCarrier y) ∧
      (GroupSingletonClassifier (append (append (append x y) BHist.Empty) BHist.Empty)
        BHist.Empty <-> GroupSingletonCarrier x ∧ GroupSingletonCarrier y) := by
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  constructor
  · constructor
    · intro carrier
      have outerSplit := append_eq_empty_iff.mp carrier
      have middleSplit := append_eq_empty_iff.mp outerSplit.left
      exact append_eq_empty_iff.mp middleSplit.left
    · intro carriers
      have productCarrier : GroupSingletonCarrier (append x y) :=
        append_eq_empty_iff.mpr carriers
      have terminalCarrier : GroupSingletonCarrier (append (append x y) BHist.Empty) :=
        append_eq_empty_iff.mpr (And.intro productCarrier emptyCarrier)
      exact append_eq_empty_iff.mpr (And.intro terminalCarrier emptyCarrier)
  · constructor
    · intro classified
      have outerSplit := append_eq_empty_iff.mp classified.left
      have middleSplit := append_eq_empty_iff.mp outerSplit.left
      exact append_eq_empty_iff.mp middleSplit.left
    · intro carriers
      have productCarrier : GroupSingletonCarrier (append x y) :=
        append_eq_empty_iff.mpr carriers
      have terminalCarrier : GroupSingletonCarrier (append (append x y) BHist.Empty) :=
        append_eq_empty_iff.mpr (And.intro productCarrier emptyCarrier)
      have commutatorCarrier :
          GroupSingletonCarrier (append (append (append x y) BHist.Empty) BHist.Empty) :=
        append_eq_empty_iff.mpr (And.intro terminalCarrier emptyCarrier)
      exact And.intro commutatorCarrier
        (And.intro emptyCarrier commutatorCarrier)

theorem GroupSingletonCommutator_carrier_classifier_exactness {x y : BHist} :
    let comm : BHist := append (append (append x y) BHist.Empty) BHist.Empty
    (GroupSingletonCarrier comm <-> GroupSingletonCarrier x ∧ GroupSingletonCarrier y) ∧
      (GroupSingletonClassifier comm BHist.Empty <->
        GroupSingletonCarrier x ∧ GroupSingletonCarrier y) := by
  dsimp
  constructor
  · constructor
    · intro carrierComm
      have outerSplit := append_eq_empty_iff.mp carrierComm
      have middleSplit := append_eq_empty_iff.mp outerSplit.left
      exact append_eq_empty_iff.mp middleSplit.left
    · intro carriers
      have productCarrier : GroupSingletonCarrier (append x y) :=
        append_eq_empty_iff.mpr carriers
      have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
      have middleCarrier : GroupSingletonCarrier (append (append x y) BHist.Empty) :=
        append_eq_empty_iff.mpr (And.intro productCarrier emptyCarrier)
      exact append_eq_empty_iff.mpr (And.intro middleCarrier emptyCarrier)
  · constructor
    · intro classified
      have outerSplit := GroupSingletonClassifier_append_unit_split_iff.mp classified
      have middleSplit := append_eq_empty_iff.mp outerSplit.left
      exact append_eq_empty_iff.mp middleSplit.left
    · intro carriers
      have productCarrier : GroupSingletonCarrier (append x y) :=
        append_eq_empty_iff.mpr carriers
      have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
      have middleCarrier : GroupSingletonCarrier (append (append x y) BHist.Empty) :=
        append_eq_empty_iff.mpr (And.intro productCarrier emptyCarrier)
      have commCarrier :
          GroupSingletonCarrier (append (append (append x y) BHist.Empty) BHist.Empty) :=
        append_eq_empty_iff.mpr (And.intro middleCarrier emptyCarrier)
      exact GroupSingletonClassifier_append_unit_split_iff.mpr
        (And.intro commCarrier emptyCarrier)

end BEDC.Derived.GroupUp
