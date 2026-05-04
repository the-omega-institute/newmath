import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem CommRingSingletonCarrier_visible_absurd {p : BHist} :
    (CommRingSingletonCarrier (BHist.e0 p) -> False) ∧
      (CommRingSingletonCarrier (BHist.e1 p) -> False) := by
  constructor
  · intro carrier
    exact not_hsame_e0_empty carrier
  · intro carrier
    exact not_hsame_e1_empty carrier

theorem concrete_singleton_history_commring_laws :
    let Carrier : BHist -> Prop := fun h => hsame h BHist.Empty
    let Classifier : BHist -> BHist -> Prop :=
      fun h k => Carrier h ∧ Carrier k ∧ hsame h k
    let add : BHist -> BHist -> BHist := append
    let neg : BHist -> BHist := fun _ => BHist.Empty
    let zero : BHist := BHist.Empty
    let mul : BHist -> BHist -> BHist := append
    let one : BHist := BHist.Empty
    Carrier zero ∧
      (∀ {x y : BHist}, Carrier x -> Carrier y -> Carrier (add x y)) ∧
      (∀ {x : BHist}, Carrier x -> Carrier (neg x)) ∧
      (∀ {x y : BHist}, Carrier x -> Carrier y -> Carrier (mul x y)) ∧
      (∀ {x : BHist}, Carrier x -> Classifier (add zero x) x) ∧
      (∀ {x : BHist}, Carrier x -> Classifier (add x zero) x) ∧
      (∀ {x y : BHist}, Carrier x -> Carrier y -> Classifier (mul x y) (mul y x)) := by
  dsimp
  constructor
  · exact hsame_refl BHist.Empty
  · constructor
    · intro x y carrierX carrierY
      cases carrierX
      cases carrierY
      rfl
    · constructor
      · intro x _carrierX
        exact hsame_refl BHist.Empty
      · constructor
        · intro x y carrierX carrierY
          cases carrierX
          cases carrierY
          rfl
        · constructor
          · intro x carrierX
            cases carrierX
            exact And.intro (hsame_refl BHist.Empty)
              (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
          · constructor
            · intro x carrierX
              cases carrierX
              exact And.intro (hsame_refl BHist.Empty)
                (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))
            · intro x y carrierX carrierY
              cases carrierX
              cases carrierY
              exact And.intro (hsame_refl BHist.Empty)
                (And.intro (hsame_refl BHist.Empty) (hsame_refl BHist.Empty))

theorem CommRingSingletonCarrier_append_visible_head_absurd {h k : BHist} :
    (CommRingSingletonCarrier (append (BHist.e0 h) k) -> False) ∧
      (CommRingSingletonCarrier (append (BHist.e1 h) k) -> False) := by
  constructor
  · intro carrier
    have emptyParts := append_eq_empty_iff.mp carrier
    exact not_hsame_e0_empty emptyParts.left
  · intro carrier
    have emptyParts := append_eq_empty_iff.mp carrier
    exact not_hsame_e1_empty emptyParts.left

theorem CommRingSingletonCarrier_append_visible_tail_absurd {p q : BHist} :
    (CommRingSingletonCarrier (append p (BHist.e0 q)) -> False) ∧
      (CommRingSingletonCarrier (append p (BHist.e1 q)) -> False) := by
  constructor
  · intro carrier
    have emptyParts := append_eq_empty_iff.mp carrier
    exact not_hsame_e0_empty emptyParts.right
  · intro carrier
    have emptyParts := append_eq_empty_iff.mp carrier
    exact not_hsame_e1_empty emptyParts.right

theorem CommRingSingletonCarrier_append_comm_iff {h k : BHist} :
    CommRingSingletonCarrier (append h k) <-> CommRingSingletonCarrier (append k h) := by
  constructor
  · intro carrier
    have parts := append_eq_empty_iff.mp carrier
    exact append_eq_empty_iff.mpr (And.intro parts.right parts.left)
  · intro carrier
    have parts := append_eq_empty_iff.mp carrier
    exact append_eq_empty_iff.mpr (And.intro parts.right parts.left)

theorem commringSingletonEmptyClassifier_mul_context_carrier_iff {L R x y out : BHist}
    (carrierL : commringSingletonEmptyCarrier L) (carrierR : commringSingletonEmptyCarrier R) :
    commringSingletonEmptyClassifier (append L (commringSingletonEmptyMul x y))
      (append R out) <-> commringSingletonEmptyCarrier out := by
  constructor
  · intro classified
    exact (append_eq_empty_iff.mp classified.right.left).right
  · intro carrierOut
    have leftCarrier :
        commringSingletonEmptyCarrier (append L (commringSingletonEmptyMul x y)) := by
      exact append_eq_empty_iff.mpr (And.intro carrierL (hsame_refl BHist.Empty))
    have rightCarrier : commringSingletonEmptyCarrier (append R out) := by
      exact append_eq_empty_iff.mpr (And.intro carrierR carrierOut)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem commringSingletonEmptyClassifier_operation_context_carrier_package {L R x y out : BHist}
    (carrierL : commringSingletonEmptyCarrier L) (carrierR : commringSingletonEmptyCarrier R) :
    (commringSingletonEmptyClassifier (append L (commringSingletonEmptyAdd x y))
      (append R out) <-> commringSingletonEmptyCarrier out) ∧
    (commringSingletonEmptyClassifier (append L (commringSingletonEmptyNeg x))
      (append R out) <-> commringSingletonEmptyCarrier out) ∧
    (commringSingletonEmptyClassifier (append L (commringSingletonEmptyMul x y))
      (append R out) <-> commringSingletonEmptyCarrier out) := by
  have emptyEndpoint : commringSingletonEmptyCarrier BHist.Empty := hsame_refl BHist.Empty
  have addIff :
      commringSingletonEmptyClassifier (append L (commringSingletonEmptyAdd x y))
        (append R out) <-> commringSingletonEmptyCarrier out := by
    constructor
    · intro classified
      exact (append_eq_empty_iff.mp classified.right.left).right
    · intro carrierOut
      have leftCarrier :
          commringSingletonEmptyCarrier (append L (commringSingletonEmptyAdd x y)) :=
        append_eq_empty_iff.mpr (And.intro carrierL emptyEndpoint)
      have rightCarrier : commringSingletonEmptyCarrier (append R out) :=
        append_eq_empty_iff.mpr (And.intro carrierR carrierOut)
      exact And.intro leftCarrier
        (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
  have negIff :
      commringSingletonEmptyClassifier (append L (commringSingletonEmptyNeg x))
        (append R out) <-> commringSingletonEmptyCarrier out := by
    constructor
    · intro classified
      exact (append_eq_empty_iff.mp classified.right.left).right
    · intro carrierOut
      have leftCarrier :
          commringSingletonEmptyCarrier (append L (commringSingletonEmptyNeg x)) :=
        append_eq_empty_iff.mpr (And.intro carrierL emptyEndpoint)
      have rightCarrier : commringSingletonEmptyCarrier (append R out) :=
        append_eq_empty_iff.mpr (And.intro carrierR carrierOut)
      exact And.intro leftCarrier
        (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))
  exact And.intro addIff
    (And.intro negIff
      (commringSingletonEmptyClassifier_mul_context_carrier_iff carrierL carrierR))

theorem CommRingSingletonClassifier_append_context_cancel_iff {L R Q S : BHist} :
    CommRingSingletonCarrier L -> CommRingSingletonCarrier R ->
      (CommRingSingletonClassifier (append L Q) (append R S) <->
        CommRingSingletonClassifier Q S) := by
  intro carrierL carrierR
  constructor
  · intro classified
    have leftSplit := append_eq_empty_iff.mp classified.left
    have rightSplit := append_eq_empty_iff.mp classified.right.left
    exact And.intro leftSplit.right
      (And.intro rightSplit.right (hsame_trans leftSplit.right (hsame_symm rightSplit.right)))
  · intro classified
    have leftCarrier : CommRingSingletonCarrier (append L Q) :=
      append_eq_empty_iff.mpr (And.intro carrierL classified.left)
    have rightCarrier : CommRingSingletonCarrier (append R S) :=
      append_eq_empty_iff.mpr (And.intro carrierR classified.right.left)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem CommRingSingletonClassifier_append_context_carrier_split {L R Q S : BHist} :
    CommRingSingletonClassifier (append L Q) (append R S) ->
      CommRingSingletonCarrier L ∧ CommRingSingletonCarrier Q ∧
        CommRingSingletonCarrier R ∧ CommRingSingletonCarrier S := by
  intro classified
  have leftSplit := append_eq_empty_iff.mp classified.left
  have rightSplit := append_eq_empty_iff.mp classified.right.left
  exact And.intro leftSplit.left
    (And.intro leftSplit.right (And.intro rightSplit.left rightSplit.right))

theorem CommRingSingletonClassifier_append_comm_congr {h h' k k' : BHist} :
    CommRingSingletonClassifier (append h k) (append h' k') ->
      CommRingSingletonClassifier (append k h) (append k' h') := by
  intro classified
  have leftParts := append_eq_empty_iff.mp classified.left
  have rightParts := append_eq_empty_iff.mp classified.right.left
  have leftCarrier : CommRingSingletonCarrier (append k h) :=
    append_eq_empty_iff.mpr (And.intro leftParts.right leftParts.left)
  have rightCarrier : CommRingSingletonCarrier (append k' h') :=
    append_eq_empty_iff.mpr (And.intro rightParts.right rightParts.left)
  exact And.intro leftCarrier
    (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem CommRingSingletonClassifier_append_comm_carrier_iff {h k : BHist} :
    CommRingSingletonClassifier (append h k) (append k h) <->
      CommRingSingletonCarrier h ∧ CommRingSingletonCarrier k := by
  constructor
  · intro classified
    exact append_eq_empty_iff.mp classified.left
  · intro carriers
    have leftCarrier : CommRingSingletonCarrier (append h k) :=
      append_eq_empty_iff.mpr (And.intro carriers.left carriers.right)
    have rightCarrier : CommRingSingletonCarrier (append k h) :=
      append_eq_empty_iff.mpr (And.intro carriers.right carriers.left)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

theorem CommRingSingletonClassifier_append_assoc_carrier_iff {a b c : BHist} :
    CommRingSingletonClassifier (append (append a b) c) (append a (append b c)) <->
      CommRingSingletonCarrier a ∧ CommRingSingletonCarrier b ∧ CommRingSingletonCarrier c := by
  constructor
  · intro classified
    have leftOuter := append_eq_empty_iff.mp classified.left
    have leftInner := append_eq_empty_iff.mp leftOuter.left
    exact And.intro leftInner.left (And.intro leftInner.right leftOuter.right)
  · intro carriers
    have leftInner : CommRingSingletonCarrier (append a b) :=
      append_eq_empty_iff.mpr (And.intro carriers.left carriers.right.left)
    have leftCarrier : CommRingSingletonCarrier (append (append a b) c) :=
      append_eq_empty_iff.mpr (And.intro leftInner carriers.right.right)
    have rightInner : CommRingSingletonCarrier (append b c) :=
      append_eq_empty_iff.mpr (And.intro carriers.right.left carriers.right.right)
    have rightCarrier : CommRingSingletonCarrier (append a (append b c)) :=
      append_eq_empty_iff.mpr (And.intro carriers.left rightInner)
    exact And.intro leftCarrier
      (And.intro rightCarrier (hsame_trans leftCarrier (hsame_symm rightCarrier)))

end BEDC.Derived.CommRingUp
