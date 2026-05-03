import BEDC.Derived.FieldUp.RatDenomContextPair
import BEDC.Derived.FieldUp.RatDenomUnit

namespace BEDC.Derived.FieldUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.Derived.RatUp

def RatDenomUnitContextualAction (p q l r h : BHist) : BHist :=
  append p (append (append (append l h) r) q)

theorem RatDenomUnitContextualAction_empty_endpoint_composition
    {h l r l' r' p q p' q' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty ->
        hsame
          (RatDenomUnitContextualAction p' q' l' r'
            (RatDenomUnitContextualAction p q l r h))
          (RatDenomUnitContextualAction p' q' (append l' l) (append r r') h) := by
  intro sameP sameQ sameP' sameQ'
  cases sameP
  cases sameQ
  cases sameP'
  cases sameQ'
  simpa [RatDenomUnitContextualAction, append_empty_left, append_empty_right, append_assoc]
    using hsame_refl (append l' (append l (append h (append r r'))))

theorem field_rat_denominator_contextual_action_unit_support_iff {h l r p q : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> RatDenomUnitCarrier h ->
      RatDenomUnitCarrier l -> RatDenomUnitCarrier r ->
        (RatHistoryCarrier l -> False) -> (RatHistoryCarrier r -> False) ->
          (RatHistoryCarrier (append p (append (append (append l h) r) q)) <->
            RatHistoryCarrier h) := by
  intro sameP sameQ carrierH carrierL carrierR notRatL notRatR
  have contextSame :
      hsame (append p (append (append (append l h) r) q)) (append (append l h) r) := by
    cases sameP
    cases sameQ
    exact hsame_trans
      (append_empty_left (append (append (append l h) r) BHist.Empty))
      (append_empty_right (append (append l h) r))
  have contextRat :
      RatHistoryCarrier (append p (append (append (append l h) r) q)) <->
        RatHistoryCarrier (append (append l h) r) := by
    constructor
    · intro ratContext
      exact RatHistoryCarrier_hsame_transport contextSame ratContext
    · intro ratCore
      exact RatHistoryCarrier_hsame_transport (hsame_symm contextSame) ratCore
  have supportRat :
      RatHistoryCarrier (append (append l h) r) <->
        RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r :=
    field_rat_denominator_empty_unit_bilateral_multiplication_support_exactness carrierH carrierL
      carrierR
  constructor
  · intro ratContext
    have ratCore : RatHistoryCarrier (append (append l h) r) := Iff.mp contextRat ratContext
    have support : RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r :=
      Iff.mp supportRat ratCore
    cases support with
    | inl ratL =>
        exact False.elim (notRatL ratL)
    | inr tailSupport =>
        cases tailSupport with
        | inl ratH =>
            exact ratH
        | inr ratR =>
            exact False.elim (notRatR ratR)
  · intro ratH
    have support : RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r :=
      Or.inr (Or.inl ratH)
    have ratCore : RatHistoryCarrier (append (append l h) r) := Iff.mpr supportRat support
    exact Iff.mpr contextRat ratCore

theorem field_rat_denominator_contextual_action_composition_support_laws
    {p q p' q' h l r l' r' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitCarrier l ->
        RatDenomUnitCarrier r -> RatDenomUnitCarrier l' -> RatDenomUnitCarrier r' ->
          RatDenomUnitCarrier
            (RatDenomUnitContextualAction p' q' l' r'
              (RatDenomUnitContextualAction p q l r h)) ∧
          RatDenomUnitClassifier
            (RatDenomUnitContextualAction p' q' l' r'
              (RatDenomUnitContextualAction p q l r h))
            (RatDenomUnitContextualAction p' q' (append l' l) (append r r') h) ∧
          (RatHistoryCarrier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h)) <->
            RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier h ∨
              RatHistoryCarrier r ∨ RatHistoryCarrier r') := by
  intro sameP sameQ sameP' sameQ' carrierH carrierL carrierR carrierL' carrierR'
  let inner := RatDenomUnitContextualAction p q l r h
  let nested := RatDenomUnitContextualAction p' q' l' r' inner
  let target := RatDenomUnitContextualAction p' q' (append l' l) (append r r') h
  have innerCoreSame : hsame inner (append (append l h) r) := by
    unfold inner RatDenomUnitContextualAction
    cases sameP
    cases sameQ
    exact hsame_trans
      (append_empty_left (append (append (append l h) r) BHist.Empty))
      (append_empty_right (append (append l h) r))
  have carrierLH : RatDenomUnitCarrier (append l h) :=
    RatDenomUnitCarrier_continuation_closed carrierL carrierH (cont_intro rfl)
  have carrierLHR : RatDenomUnitCarrier (append (append l h) r) :=
    RatDenomUnitCarrier_continuation_closed carrierLH carrierR (cont_intro rfl)
  have carrierInner : RatDenomUnitCarrier inner :=
    RatDenomUnitCarrier_hsame_transport (hsame_symm innerCoreSame) carrierLHR
  have nestedCoreSame : hsame nested (append (append l' inner) r') := by
    unfold nested RatDenomUnitContextualAction
    cases sameP'
    cases sameQ'
    exact hsame_trans
      (append_empty_left (append (append (append l' inner) r') BHist.Empty))
      (append_empty_right (append (append l' inner) r'))
  have carrierL'Inner : RatDenomUnitCarrier (append l' inner) :=
    RatDenomUnitCarrier_continuation_closed carrierL' carrierInner (cont_intro rfl)
  have carrierNestedCore : RatDenomUnitCarrier (append (append l' inner) r') :=
    RatDenomUnitCarrier_continuation_closed carrierL'Inner carrierR' (cont_intro rfl)
  have carrierNested : RatDenomUnitCarrier nested :=
    RatDenomUnitCarrier_hsame_transport (hsame_symm nestedCoreSame) carrierNestedCore
  have carrierL'L : RatDenomUnitCarrier (append l' l) :=
    RatDenomUnitCarrier_continuation_closed carrierL' carrierL (cont_intro rfl)
  have carrierRR' : RatDenomUnitCarrier (append r r') :=
    RatDenomUnitCarrier_continuation_closed carrierR carrierR' (cont_intro rfl)
  have carrierL'LH : RatDenomUnitCarrier (append (append l' l) h) :=
    RatDenomUnitCarrier_continuation_closed carrierL'L carrierH (cont_intro rfl)
  have carrierTargetCore :
      RatDenomUnitCarrier (append (append (append l' l) h) (append r r')) :=
    RatDenomUnitCarrier_continuation_closed carrierL'LH carrierRR' (cont_intro rfl)
  have targetCoreSame : hsame target (append (append (append l' l) h) (append r r')) := by
    unfold target RatDenomUnitContextualAction
    cases sameP'
    cases sameQ'
    exact hsame_trans
      (append_empty_left
        (append (append (append (append l' l) h) (append r r')) BHist.Empty))
      (append_empty_right (append (append (append l' l) h) (append r r')))
  have carrierTarget : RatDenomUnitCarrier target :=
    RatDenomUnitCarrier_hsame_transport (hsame_symm targetCoreSame) carrierTargetCore
  have nestedTargetSame : hsame nested target := by
    apply hsame_trans nestedCoreSame
    apply hsame_trans
    · exact congrArg (fun x => append (append l' x) r') innerCoreSame
    apply hsame_trans
    ·
      exact
        (congrArg (fun x => append x r') (append_assoc l' (append l h) r).symm).trans
          ((append_assoc (append l' (append l h)) r r').trans
            (congrArg (fun x => append x (append r r')) (append_assoc l' l h).symm))
    · exact hsame_symm targetCoreSame
  have nestedRatCore :
      RatHistoryCarrier nested <-> RatHistoryCarrier (append (append l' inner) r') := by
    constructor
    · intro ratNested
      exact RatHistoryCarrier_hsame_transport nestedCoreSame ratNested
    · intro ratCore
      exact RatHistoryCarrier_hsame_transport (hsame_symm nestedCoreSame) ratCore
  have outerSupport :
      RatHistoryCarrier (append (append l' inner) r') <->
        RatHistoryCarrier l' ∨ RatHistoryCarrier inner ∨ RatHistoryCarrier r' :=
    field_rat_denominator_empty_unit_bilateral_multiplication_support_exactness carrierInner
      carrierL' carrierR'
  have innerRatCore :
      RatHistoryCarrier inner <-> RatHistoryCarrier (append (append l h) r) := by
    constructor
    · intro ratInner
      exact RatHistoryCarrier_hsame_transport innerCoreSame ratInner
    · intro ratCore
      exact RatHistoryCarrier_hsame_transport (hsame_symm innerCoreSame) ratCore
  have innerSupport :
      RatHistoryCarrier (append (append l h) r) <->
        RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r :=
    field_rat_denominator_empty_unit_bilateral_multiplication_support_exactness carrierH carrierL
      carrierR
  have supportLaw :
      RatHistoryCarrier nested <->
        RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier h ∨
          RatHistoryCarrier r ∨ RatHistoryCarrier r' := by
    constructor
    · intro ratNested
      have outer :
          RatHistoryCarrier l' ∨ RatHistoryCarrier inner ∨ RatHistoryCarrier r' :=
        Iff.mp outerSupport (Iff.mp nestedRatCore ratNested)
      cases outer with
      | inl ratL' =>
          exact Or.inl ratL'
      | inr outerTail =>
          cases outerTail with
          | inl ratInner =>
              have innerData :
                  RatHistoryCarrier l ∨ RatHistoryCarrier h ∨ RatHistoryCarrier r :=
                Iff.mp innerSupport (Iff.mp innerRatCore ratInner)
              cases innerData with
              | inl ratL =>
                  exact Or.inr (Or.inl ratL)
              | inr innerTail =>
                  cases innerTail with
                  | inl ratH =>
                      exact Or.inr (Or.inr (Or.inl ratH))
                  | inr ratR =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl ratR)))
          | inr ratR' =>
              exact Or.inr (Or.inr (Or.inr (Or.inr ratR')))
    · intro support
      have outer :
          RatHistoryCarrier l' ∨ RatHistoryCarrier inner ∨ RatHistoryCarrier r' := by
        cases support with
        | inl ratL' =>
            exact Or.inl ratL'
        | inr supportTail =>
            cases supportTail with
            | inl ratL =>
                have innerCoreRat : RatHistoryCarrier (append (append l h) r) :=
                  Iff.mpr innerSupport (Or.inl ratL)
                exact Or.inr (Or.inl (Iff.mpr innerRatCore innerCoreRat))
            | inr supportTail =>
                cases supportTail with
                | inl ratH =>
                    have innerCoreRat : RatHistoryCarrier (append (append l h) r) :=
                      Iff.mpr innerSupport (Or.inr (Or.inl ratH))
                    exact Or.inr (Or.inl (Iff.mpr innerRatCore innerCoreRat))
                | inr supportTail =>
                    cases supportTail with
                    | inl ratR =>
                        have innerCoreRat : RatHistoryCarrier (append (append l h) r) :=
                          Iff.mpr innerSupport (Or.inr (Or.inr ratR))
                        exact Or.inr (Or.inl (Iff.mpr innerRatCore innerCoreRat))
                    | inr ratR' =>
                        exact Or.inr (Or.inr ratR')
      exact Iff.mpr nestedRatCore (Iff.mpr outerSupport outer)
  exact ⟨carrierNested, ⟨carrierNested, carrierTarget, nestedTargetSame⟩, supportLaw⟩

theorem RatDenomUnitContextualAction_pair_support_transport_iff
    {p q p' q' h l r s t l' r' s' t' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitClassifier l s ->
        RatDenomUnitClassifier r t -> RatDenomUnitClassifier l' s' ->
          RatDenomUnitClassifier r' t' ->
            (RatHistoryCarrier
                (RatDenomUnitContextualAction p' q' l' r'
                  (RatDenomUnitContextualAction p q l r h)) <->
              RatHistoryCarrier
                (RatDenomUnitContextualAction p' q' s' t'
                  (RatDenomUnitContextualAction p q s t h))) := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
  have leftLaws :=
    field_rat_denominator_contextual_action_composition_support_laws sameP sameQ sameP'
      sameQ' carrierH classifiedL.left classifiedR.left classifiedL'.left classifiedR'.left
  have rightLaws :=
    field_rat_denominator_contextual_action_composition_support_laws sameP sameQ sameP'
      sameQ' carrierH classifiedL.right.left classifiedR.right.left classifiedL'.right.left
      classifiedR'.right.left
  have leftContextSupport :
      RatHistoryCarrier (append (append l' l) (append r r')) <->
        RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier r ∨
          RatHistoryCarrier r' :=
    RatDenomContextPair_product_strict_support_iff classifiedL.left classifiedR.left
      classifiedL'.left classifiedR'.left
  have rightContextSupport :
      RatHistoryCarrier (append (append s' s) (append t t')) <->
        RatHistoryCarrier s' ∨ RatHistoryCarrier s ∨ RatHistoryCarrier t ∨
          RatHistoryCarrier t' :=
    RatDenomContextPair_product_strict_support_iff classifiedL.right.left
      classifiedR.right.left classifiedL'.right.left classifiedR'.right.left
  have contextTransport :
      RatHistoryCarrier (append (append l' l) (append r r')) <->
        RatHistoryCarrier (append (append s' s) (append t t')) :=
    RatDenomContextPair_product_strict_support_transport classifiedL classifiedR
      classifiedL' classifiedR'
  have supportTransport :
      (RatHistoryCarrier l' ∨ RatHistoryCarrier l ∨ RatHistoryCarrier h ∨
          RatHistoryCarrier r ∨ RatHistoryCarrier r') <->
        (RatHistoryCarrier s' ∨ RatHistoryCarrier s ∨ RatHistoryCarrier h ∨
          RatHistoryCarrier t ∨ RatHistoryCarrier t') := by
    constructor
    · intro support
      cases support with
      | inl ratL' =>
          have rightProduct :
              RatHistoryCarrier (append (append s' s) (append t t')) :=
            Iff.mp contextTransport (Iff.mpr leftContextSupport (Or.inl ratL'))
          have rightSupport := Iff.mp rightContextSupport rightProduct
          cases rightSupport with
          | inl ratS' =>
              exact Or.inl ratS'
          | inr rightTail =>
              cases rightTail with
              | inl ratS =>
                  exact Or.inr (Or.inl ratS)
              | inr rightTail =>
                  cases rightTail with
                  | inl ratT =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl ratT)))
                  | inr ratT' =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr ratT')))
      | inr supportTail =>
          cases supportTail with
          | inl ratL =>
              have rightProduct :
                  RatHistoryCarrier (append (append s' s) (append t t')) :=
                Iff.mp contextTransport (Iff.mpr leftContextSupport (Or.inr (Or.inl ratL)))
              have rightSupport := Iff.mp rightContextSupport rightProduct
              cases rightSupport with
              | inl ratS' =>
                  exact Or.inl ratS'
              | inr rightTail =>
                  cases rightTail with
                  | inl ratS =>
                      exact Or.inr (Or.inl ratS)
                  | inr rightTail =>
                      cases rightTail with
                      | inl ratT =>
                          exact Or.inr (Or.inr (Or.inr (Or.inl ratT)))
                      | inr ratT' =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr ratT')))
          | inr supportTail =>
              cases supportTail with
              | inl ratH =>
                  exact Or.inr (Or.inr (Or.inl ratH))
              | inr supportTail =>
                  cases supportTail with
                  | inl ratR =>
                      have rightProduct :
                          RatHistoryCarrier (append (append s' s) (append t t')) :=
                        Iff.mp contextTransport
                          (Iff.mpr leftContextSupport (Or.inr (Or.inr (Or.inl ratR))))
                      have rightSupport := Iff.mp rightContextSupport rightProduct
                      cases rightSupport with
                      | inl ratS' =>
                          exact Or.inl ratS'
                      | inr rightTail =>
                          cases rightTail with
                          | inl ratS =>
                              exact Or.inr (Or.inl ratS)
                          | inr rightTail =>
                              cases rightTail with
                              | inl ratT =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inl ratT)))
                              | inr ratT' =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr ratT')))
                  | inr ratR' =>
                      have rightProduct :
                          RatHistoryCarrier (append (append s' s) (append t t')) :=
                        Iff.mp contextTransport
                          (Iff.mpr leftContextSupport (Or.inr (Or.inr (Or.inr ratR'))))
                      have rightSupport := Iff.mp rightContextSupport rightProduct
                      cases rightSupport with
                      | inl ratS' =>
                          exact Or.inl ratS'
                      | inr rightTail =>
                          cases rightTail with
                          | inl ratS =>
                              exact Or.inr (Or.inl ratS)
                          | inr rightTail =>
                              cases rightTail with
                              | inl ratT =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inl ratT)))
                              | inr ratT' =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr ratT')))
    · intro support
      cases support with
      | inl ratS' =>
          have leftProduct :
              RatHistoryCarrier (append (append l' l) (append r r')) :=
            Iff.mpr contextTransport (Iff.mpr rightContextSupport (Or.inl ratS'))
          have leftSupport := Iff.mp leftContextSupport leftProduct
          cases leftSupport with
          | inl ratL' =>
              exact Or.inl ratL'
          | inr leftTail =>
              cases leftTail with
              | inl ratL =>
                  exact Or.inr (Or.inl ratL)
              | inr leftTail =>
                  cases leftTail with
                  | inl ratR =>
                      exact Or.inr (Or.inr (Or.inr (Or.inl ratR)))
                  | inr ratR' =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr ratR')))
      | inr supportTail =>
          cases supportTail with
          | inl ratS =>
              have leftProduct :
                  RatHistoryCarrier (append (append l' l) (append r r')) :=
                Iff.mpr contextTransport (Iff.mpr rightContextSupport (Or.inr (Or.inl ratS)))
              have leftSupport := Iff.mp leftContextSupport leftProduct
              cases leftSupport with
              | inl ratL' =>
                  exact Or.inl ratL'
              | inr leftTail =>
                  cases leftTail with
                  | inl ratL =>
                      exact Or.inr (Or.inl ratL)
                  | inr leftTail =>
                      cases leftTail with
                      | inl ratR =>
                          exact Or.inr (Or.inr (Or.inr (Or.inl ratR)))
                      | inr ratR' =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr ratR')))
          | inr supportTail =>
              cases supportTail with
              | inl ratH =>
                  exact Or.inr (Or.inr (Or.inl ratH))
              | inr supportTail =>
                  cases supportTail with
                  | inl ratT =>
                      have leftProduct :
                          RatHistoryCarrier (append (append l' l) (append r r')) :=
                        Iff.mpr contextTransport
                          (Iff.mpr rightContextSupport (Or.inr (Or.inr (Or.inl ratT))))
                      have leftSupport := Iff.mp leftContextSupport leftProduct
                      cases leftSupport with
                      | inl ratL' =>
                          exact Or.inl ratL'
                      | inr leftTail =>
                          cases leftTail with
                          | inl ratL =>
                              exact Or.inr (Or.inl ratL)
                          | inr leftTail =>
                              cases leftTail with
                              | inl ratR =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inl ratR)))
                              | inr ratR' =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr ratR')))
                  | inr ratT' =>
                      have leftProduct :
                          RatHistoryCarrier (append (append l' l) (append r r')) :=
                        Iff.mpr contextTransport
                          (Iff.mpr rightContextSupport (Or.inr (Or.inr (Or.inr ratT'))))
                      have leftSupport := Iff.mp leftContextSupport leftProduct
                      cases leftSupport with
                      | inl ratL' =>
                          exact Or.inl ratL'
                      | inr leftTail =>
                          cases leftTail with
                          | inl ratL =>
                              exact Or.inr (Or.inl ratL)
                          | inr leftTail =>
                              cases leftTail with
                              | inl ratR =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inl ratR)))
                              | inr ratR' =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr ratR')))
  constructor
  · intro leftCarrier
    exact Iff.mpr rightLaws.right.right
      (Iff.mp supportTransport (Iff.mp leftLaws.right.right leftCarrier))
  · intro rightCarrier
    exact Iff.mpr leftLaws.right.right
      (Iff.mpr supportTransport (Iff.mp rightLaws.right.right rightCarrier))

theorem RatDenomUnitContextualAction_pair_classifier_transport
    {p q p' q' h l r s t l' r' s' t' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitClassifier l s ->
        RatDenomUnitClassifier r t -> RatDenomUnitClassifier l' s' ->
          RatDenomUnitClassifier r' t' ->
            RatDenomUnitClassifier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h))
              (RatDenomUnitContextualAction p' q' s' t'
                (RatDenomUnitContextualAction p q s t h)) := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
  have leftLaws :=
    field_rat_denominator_contextual_action_composition_support_laws sameP sameQ sameP'
      sameQ' carrierH classifiedL.left classifiedR.left classifiedL'.left classifiedR'.left
  have rightLaws :=
    field_rat_denominator_contextual_action_composition_support_laws sameP sameQ sameP'
      sameQ' carrierH classifiedL.right.left classifiedR.right.left classifiedL'.right.left
      classifiedR'.right.left
  have classifiedLeftProduct :
      RatDenomUnitClassifier (append l' l) (append s' s) :=
    RatDenomUnitClassifier_continuation_closed classifiedL' classifiedL
      (cont_intro rfl) (cont_intro rfl)
  have classifiedRightProduct :
      RatDenomUnitClassifier (append r r') (append t t') :=
    RatDenomUnitClassifier_continuation_closed classifiedR classifiedR'
      (cont_intro rfl) (cont_intro rfl)
  have classifiedH : RatDenomUnitClassifier h h :=
    ⟨carrierH, carrierH, hsame_refl h⟩
  have classifiedLeftCore :
      RatDenomUnitClassifier (append (append l' l) h) (append (append s' s) h) :=
    RatDenomUnitClassifier_continuation_closed classifiedLeftProduct classifiedH
      (cont_intro rfl) (cont_intro rfl)
  have classifiedCollectedCore :
      RatDenomUnitClassifier
        (append (append (append l' l) h) (append r r'))
        (append (append (append s' s) h) (append t t')) :=
    RatDenomUnitClassifier_continuation_closed classifiedLeftCore classifiedRightProduct
      (cont_intro rfl) (cont_intro rfl)
  have classifiedCollected :
      RatDenomUnitClassifier
        (RatDenomUnitContextualAction p' q' (append l' l) (append r r') h)
        (RatDenomUnitContextualAction p' q' (append s' s) (append t t') h) := by
    exact Iff.mpr
      (RatDenomUnitClassifier_empty_context_iff sameP' sameQ' sameP' sameQ')
      classifiedCollectedCore
  have sameNested :
      hsame
        (RatDenomUnitContextualAction p' q' l' r'
          (RatDenomUnitContextualAction p q l r h))
        (RatDenomUnitContextualAction p' q' s' t'
          (RatDenomUnitContextualAction p q s t h)) :=
    hsame_trans leftLaws.right.left.right.right
      (hsame_trans classifiedCollected.right.right (hsame_symm rightLaws.right.left.right.right))
  exact ⟨leftLaws.left, rightLaws.left, sameNested⟩

theorem RatDenomUnitContextualAction_pair_transport_classifier
    {p q p' q' h l r s t l' r' s' t' : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h ->
        RatDenomUnitClassifier l s -> RatDenomUnitClassifier r t ->
          RatDenomUnitClassifier l' s' -> RatDenomUnitClassifier r' t' ->
            RatDenomUnitClassifier
              (RatDenomUnitContextualAction p' q' l' r'
                (RatDenomUnitContextualAction p q l r h))
              (RatDenomUnitContextualAction p' q' s' t'
                (RatDenomUnitContextualAction p q s t h)) := by
  intro sameP sameQ sameP' sameQ' carrierH classifiedL classifiedR classifiedL' classifiedR'
  exact RatDenomUnitContextualAction_pair_classifier_transport sameP sameQ sameP' sameQ'
    carrierH classifiedL classifiedR classifiedL' classifiedR'

theorem RatDenomUnitContextualAction_strict_support_contextual_singleton_exclusion
    {p q p' q' h l r l' r' ctx : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitCarrier l ->
        RatDenomUnitCarrier r -> RatDenomUnitCarrier l' -> RatDenomUnitCarrier r' ->
          RatHistoryCarrier h ->
            (fieldSingletonEmptyCarrier
                (append ctx
                  (RatDenomUnitContextualAction p' q' l' r'
                    (RatDenomUnitContextualAction p q l r h))) -> False) ∧
            (fieldSingletonEmptyCarrier
                (append
                  (RatDenomUnitContextualAction p' q' l' r'
                    (RatDenomUnitContextualAction p q l r h))
                  ctx) -> False) := by
  intro sameP sameQ sameP' sameQ' carrierH carrierL carrierR carrierL' carrierR' ratH
  have laws :=
    field_rat_denominator_contextual_action_composition_support_laws sameP sameQ sameP'
      sameQ' carrierH carrierL carrierR carrierL' carrierR'
  have nestedRat :
      RatHistoryCarrier
        (RatDenomUnitContextualAction p' q' l' r'
          (RatDenomUnitContextualAction p q l r h)) :=
    Iff.mpr laws.right.right (Or.inr (Or.inr (Or.inl ratH)))
  constructor
  · intro singletonLeft
    exact fieldSingletonEmptyCarrier_append_ratHistoryCarrier_absurd singletonLeft nestedRat
  · intro singletonRight
    exact fieldSingletonEmptyCarrier_append_left_ratHistoryCarrier_absurd singletonRight nestedRat

theorem RatDenomUnitContextualAction_strict_support_singleton_classifier_exclusion
    {p q p' q' h l r l' r' L R : BHist} :
    hsame p BHist.Empty -> hsame q BHist.Empty -> hsame p' BHist.Empty ->
      hsame q' BHist.Empty -> RatDenomUnitCarrier h -> RatDenomUnitCarrier l ->
        RatDenomUnitCarrier r -> RatDenomUnitCarrier l' -> RatDenomUnitCarrier r' ->
          RatHistoryCarrier h ->
            fieldSingletonEmptyClassifier
              (append L
                (RatDenomUnitContextualAction p' q' l' r'
                  (RatDenomUnitContextualAction p q l r h)))
              (append R
                (RatDenomUnitContextualAction p' q' l' r'
                  (RatDenomUnitContextualAction p q l r h))) -> False := by
  intro sameP sameQ sameP' sameQ' carrierH carrierL carrierR carrierL' carrierR' ratH
    singleton
  have laws :=
    field_rat_denominator_contextual_action_composition_support_laws sameP sameQ sameP'
      sameQ' carrierH carrierL carrierR carrierL' carrierR'
  have nestedRat :
      RatHistoryCarrier
        (RatDenomUnitContextualAction p' q' l' r'
          (RatDenomUnitContextualAction p q l r h)) :=
    Iff.mpr laws.right.right (Or.inr (Or.inr (Or.inl ratH)))
  have nestedClassifier :
      RatHistoryClassifier
        (RatDenomUnitContextualAction p' q' l' r'
          (RatDenomUnitContextualAction p q l r h))
        (RatDenomUnitContextualAction p' q' l' r'
          (RatDenomUnitContextualAction p q l r h)) :=
    ⟨nestedRat, nestedRat, hsame_refl _⟩
  exact fieldSingletonEmptyClassifier_append_RatHistoryClassifier_absurd nestedClassifier singleton

theorem RatDenomContextPair_unit_support_neutrality {h : BHist} :
    RatDenomUnitCarrier h ->
      ((RatHistoryCarrier BHist.Empty ∨ RatHistoryCarrier BHist.Empty) -> False) ∧
      (RatHistoryCarrier
        (RatDenomUnitContextualAction BHist.Empty BHist.Empty BHist.Empty BHist.Empty h) <->
        RatHistoryCarrier h) := by
  intro carrierH
  have carrierEmpty : RatDenomUnitCarrier BHist.Empty :=
    field_rat_denominator_empty_unit_continuation_monoid_laws.left
  have notRatEmpty : RatHistoryCarrier BHist.Empty -> False :=
    fun ratEmpty => RatHistoryCarrier_not_empty ratEmpty (hsame_refl BHist.Empty)
  constructor
  · intro support
    cases support with
    | inl ratEmpty =>
        exact notRatEmpty ratEmpty
    | inr ratEmpty =>
        exact notRatEmpty ratEmpty
  · exact field_rat_denominator_contextual_action_unit_support_iff
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty) carrierH carrierEmpty carrierEmpty
      notRatEmpty notRatEmpty

end BEDC.Derived.FieldUp
