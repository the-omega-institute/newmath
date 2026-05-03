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

end BEDC.Derived.CommRingUp
