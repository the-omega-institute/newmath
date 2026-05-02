import BEDC.Derived.CommRingUp

namespace BEDC.Derived.CommRingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

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

end BEDC.Derived.CommRingUp
