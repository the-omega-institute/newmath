import BEDC.Derived.GroupUp

namespace BEDC.Derived.GroupUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.MonoidUp

theorem GroupSingletonNormalizer_action_certificate {s x : BHist} :
    GroupSingletonCarrier s -> GroupSingletonCarrier x ->
      let Conj : BHist -> BHist := fun y => append (append s y) BHist.Empty
      let InvConj : BHist -> BHist := fun y => append (append BHist.Empty y) BHist.Empty
      GroupSingletonCarrier (Conj x) ∧ GroupSingletonCarrier (InvConj x) ∧
        GroupSingletonClassifier (Conj x) x ∧
          GroupSingletonClassifier (InvConj (Conj x)) x := by
  intro carrierS carrierX
  dsimp
  have emptyCarrier : GroupSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have conjCarrier : GroupSingletonCarrier (append (append s x) BHist.Empty) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro carrierS carrierX)) emptyCarrier)
  have invConjCarrier : GroupSingletonCarrier (append (append BHist.Empty x) BHist.Empty) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro emptyCarrier carrierX)) emptyCarrier)
  have invAfterConjCarrier :
      GroupSingletonCarrier (append (append BHist.Empty (append (append s x) BHist.Empty))
        BHist.Empty) :=
    append_eq_empty_iff.mpr
      (And.intro (append_eq_empty_iff.mpr (And.intro emptyCarrier conjCarrier)) emptyCarrier)
  constructor
  · exact conjCarrier
  · constructor
    · exact invConjCarrier
    · constructor
      · exact And.intro conjCarrier
          (And.intro carrierX (hsame_trans conjCarrier (hsame_symm carrierX)))
      · exact And.intro invAfterConjCarrier
          (And.intro carrierX (hsame_trans invAfterConjCarrier (hsame_symm carrierX)))

theorem MonoidHistoryClassifier_unary_append_unit_product_factor_exactness {h k : BHist} :
    MonoidHistoryClassifier UnaryHistory (append h k) BHist.Empty <->
      MonoidHistoryClassifier UnaryHistory h BHist.Empty ∧
        MonoidHistoryClassifier UnaryHistory k BHist.Empty := by
  constructor
  · intro classified
    have emptySplit := append_eq_empty_iff.mp classified.right.right
    constructor
    · exact And.intro (unary_append_left_factor classified.left)
        (And.intro unary_empty emptySplit.left)
    · exact And.intro (unary_append_right_factor classified.left)
        (And.intro unary_empty emptySplit.right)
  · intro factors
    exact And.intro (unary_append_closed factors.left.left factors.right.left)
      (And.intro unary_empty
        (append_eq_empty_iff.mpr
          (And.intro factors.left.right.right factors.right.right.right)))

end BEDC.Derived.GroupUp
