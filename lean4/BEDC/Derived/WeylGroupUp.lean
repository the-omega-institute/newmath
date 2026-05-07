import BEDC.Derived.GroupUp
import BEDC.Derived.RootSystemUp
import BEDC.FKernel.Cont.Units

namespace BEDC.Derived.WeylGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.RootSystemUp
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def WeylGroupSourceRow
    (support : ProbeBundle BHist)
    (Vector Nonzero : BHist -> Prop)
    (root word endpoint : BHist) : Prop :=
  RootSystemFiniteSupportCarrier support Vector Nonzero root ∧
    GroupSingletonCarrier word ∧ Cont root word endpoint

theorem WeylGroupSourceRow_append_closure
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {root word endpoint next product : BHist} :
    WeylGroupSourceRow support Vector Nonzero root word endpoint ->
      GroupSingletonCarrier next -> Cont endpoint next product ->
        WeylGroupSourceRow support Vector Nonzero root (append word next) product ∧
          GroupSingletonCarrier (append word next) := by
  intro row nextCarrier endpointNext
  have wordNextCarrier : GroupSingletonCarrier (append word next) :=
    append_eq_empty_iff.mpr (And.intro row.right.left nextCarrier)
  have rootWordNext : Cont root (append word next) product := by
    cases row.right.right
    cases endpointNext
    exact append_assoc root word next
  exact And.intro
    (And.intro row.left (And.intro wordNextCarrier rootWordNext))
    wordNextCarrier

theorem WeylGroupSimpleReflection_word_closure {support : ProbeBundle BHist}
    {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {alpha beta reflected word endpoint composite : BHist} :
    RootSystemFiniteSupportCarrier support Vector Nonzero alpha ->
      RootSystemFiniteSupportCarrier support Vector Nonzero beta ->
        Cont alpha beta reflected ->
          GroupSingletonCarrier word ->
            Cont reflected word endpoint ->
              Cont alpha (append beta word) composite ->
                hsame endpoint composite ∧ UnaryHistory reflected ∧ UnaryHistory endpoint := by
  intro alphaCarrier betaCarrier reflectionRoute wordCarrier wordRoute compositeRoute
  have reflectedUnary : UnaryHistory reflected :=
    RootSystemReflectionClosure_result_unary vector_unary alphaCarrier betaCarrier reflectionRoute
  have wordUnary : UnaryHistory word := by
    cases wordCarrier
    exact unary_empty
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed reflectedUnary wordUnary wordRoute
  have endpointRoute : Cont alpha (append beta word) endpoint := by
    cases wordCarrier
    cases wordRoute
    cases reflectionRoute
    exact (congrArg (append alpha) (append_empty_right beta)).symm
  exact And.intro
    (cont_deterministic endpointRoute compositeRoute)
    (And.intro reflectedUnary endpointUnary)

def WeylGroupBHistSourceRow
    (support : ProbeBundle BHist) (Vector Nonzero : BHist -> Prop)
    (root word action : BHist) : Prop :=
  RootSystemFiniteSupportCarrier support Vector Nonzero root ∧
    GroupSingletonCarrier word ∧ Cont root word action ∧ UnaryHistory action

theorem WeylGroupBHistSourceRow_simple_reflection_word_closure
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root wordA wordB actionA actionAB : BHist} :
    WeylGroupBHistSourceRow support Vector Nonzero root wordA actionA ->
      GroupSingletonCarrier wordB -> Cont actionA wordB actionAB ->
        WeylGroupBHistSourceRow support Vector Nonzero root (append wordA wordB) actionAB ∧
          hsame actionAB root ∧ GroupSingletonCarrier (append wordA wordB) := by
  intro source wordBCarrier actionStep
  have rootUnary : UnaryHistory root :=
    vector_unary source.left.right.left
  have wordAEmpty : hsame wordA BHist.Empty := source.right.left
  have wordBEmpty : hsame wordB BHist.Empty := wordBCarrier
  have wordAppendCarrier : GroupSingletonCarrier (append wordA wordB) :=
    append_eq_empty_iff.mpr (And.intro wordAEmpty wordBEmpty)
  have actionSameRoot : hsame actionA root :=
    cont_right_unit_result (by
      cases wordAEmpty
      exact source.right.right.left)
  have actionABSameActionA : hsame actionAB actionA :=
    cont_right_unit_result (by
      cases wordBEmpty
      exact actionStep)
  have actionABSameRoot : hsame actionAB root :=
    hsame_trans actionABSameActionA actionSameRoot
  have composedRow : Cont root (append wordA wordB) actionAB := by
    cases source.right.right.left
    cases actionStep
    exact append_assoc root wordA wordB
  have actionABUnary : UnaryHistory actionAB :=
    unary_transport rootUnary (hsame_symm actionABSameRoot)
  exact And.intro
    (And.intro source.left
      (And.intro wordAppendCarrier (And.intro composedRow actionABUnary)))
    (And.intro actionABSameRoot wordAppendCarrier)

theorem WeylGroupCoxeterWordLedger_row
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {root wordL wordR actionL actionR : BHist} :
    WeylGroupBHistSourceRow support Vector Nonzero root wordL actionL ->
      WeylGroupBHistSourceRow support Vector Nonzero root wordR actionR ->
        GroupSingletonClassifier wordL wordR ->
          hsame actionL actionR ∧ GroupSingletonCarrier wordL ∧ GroupSingletonCarrier wordR ∧
            Cont root wordL actionL ∧ Cont root wordR actionR := by
  intro rowL rowR classifier
  have sameActionRootL : hsame actionL root :=
    cont_right_unit_result (by
      cases classifier.left
      exact rowL.right.right.left)
  have sameActionRootR : hsame actionR root :=
    cont_right_unit_result (by
      cases classifier.right.left
      exact rowR.right.right.left)
  have sameAction : hsame actionL actionR :=
    hsame_trans sameActionRootL (hsame_symm sameActionRootR)
  exact And.intro sameAction
    (And.intro classifier.left
      (And.intro classifier.right.left
        (And.intro rowL.right.right.left rowR.right.right.left)))

theorem WeylGroupBHistSourceRow_action_classifier_stability
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root word action wordNext actionNext : BHist} :
    WeylGroupBHistSourceRow support Vector Nonzero root word action ->
      GroupSingletonCarrier wordNext -> Cont action wordNext actionNext ->
        WeylGroupBHistSourceRow support Vector Nonzero root (append word wordNext) actionNext ∧
          hsame actionNext action ∧ hsame actionNext root := by
  intro source wordNextCarrier actionStep
  have closed :=
    WeylGroupBHistSourceRow_simple_reflection_word_closure vector_unary source wordNextCarrier
      actionStep
  have actionNextSameAction : hsame actionNext action := by
    cases wordNextCarrier
    exact cont_right_unit_result actionStep
  exact And.intro closed.left (And.intro actionNextSameAction closed.right.left)

theorem WeylGroupActionClassifier_stability_transport
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root wordA wordB actionA actionB transportedAction : BHist} :
    WeylGroupBHistSourceRow support Vector Nonzero root wordA actionA ->
      GroupSingletonCarrier wordB -> Cont actionA wordB actionB ->
        hsame actionB transportedAction ->
          WeylGroupBHistSourceRow support Vector Nonzero root (append wordA wordB) actionB ∧
            UnaryHistory transportedAction ∧ hsame actionB transportedAction := by
  intro source wordBCarrier actionStep sameTransported
  have closure :
      WeylGroupBHistSourceRow support Vector Nonzero root (append wordA wordB) actionB ∧
        hsame actionB root ∧ GroupSingletonCarrier (append wordA wordB) :=
    WeylGroupBHistSourceRow_simple_reflection_word_closure
      vector_unary source wordBCarrier actionStep
  have transportedUnary : UnaryHistory transportedAction :=
    unary_transport closure.left.right.right.right sameTransported
  exact And.intro closure.left
    (And.intro transportedUnary sameTransported)

theorem WeylGroupActionClassifier_append_stability_row
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root root' wordA wordA' wordB wordB' actionA actionA' actionAB actionAB' :
      BHist} :
    WeylGroupBHistSourceRow support Vector Nonzero root wordA actionA ->
      WeylGroupBHistSourceRow support Vector Nonzero root' wordA' actionA' ->
        hsame root root' -> hsame wordA wordA' -> hsame wordB wordB' ->
          GroupSingletonCarrier wordB -> GroupSingletonCarrier wordB' ->
            Cont actionA wordB actionAB -> Cont actionA' wordB' actionAB' ->
              WeylGroupBHistSourceRow support Vector Nonzero root (append wordA wordB)
                  actionAB ∧
                WeylGroupBHistSourceRow support Vector Nonzero root' (append wordA' wordB')
                  actionAB' ∧
                  hsame (append wordA wordB) (append wordA' wordB') ∧
                    hsame actionAB actionAB' := by
  intro source source' sameRoot sameWordA sameWordB wordBCarrier wordB'Carrier
    actionStep actionStep'
  have closed :
      WeylGroupBHistSourceRow support Vector Nonzero root (append wordA wordB) actionAB ∧
        hsame actionAB root ∧ GroupSingletonCarrier (append wordA wordB) :=
    WeylGroupBHistSourceRow_simple_reflection_word_closure
      vector_unary source wordBCarrier actionStep
  have closed' :
      WeylGroupBHistSourceRow support Vector Nonzero root' (append wordA' wordB') actionAB' ∧
        hsame actionAB' root' ∧ GroupSingletonCarrier (append wordA' wordB') :=
    WeylGroupBHistSourceRow_simple_reflection_word_closure
      vector_unary source' wordB'Carrier actionStep'
  have sameWordAppend : hsame (append wordA wordB) (append wordA' wordB') := by
    cases sameWordA
    cases sameWordB
    exact hsame_refl (append wordA wordB)
  have sameAction : hsame actionAB actionAB' :=
    hsame_trans closed.right.left
      (hsame_trans sameRoot (hsame_symm closed'.right.left))
  exact And.intro closed.left
    (And.intro closed'.left (And.intro sameWordAppend sameAction))

theorem WeylGroupSimpleReflectionWord_closure_row
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {alpha beta reflected word product : BHist}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h) :
    RootSystemFiniteSupportCarrier support Vector Nonzero alpha ->
      RootSystemFiniteSupportCarrier support Vector Nonzero beta ->
        Cont alpha beta reflected -> GroupSingletonCarrier word ->
          Cont reflected word product ->
            UnaryHistory reflected ∧ UnaryHistory product ∧
              RootSystemFiniteSupportCarrier support Vector Nonzero alpha ∧
                GroupSingletonCarrier word ∧ Cont reflected word product := by
  intro alphaCarrier betaCarrier reflectionRoute wordCarrier productRoute
  have reflectedUnary : UnaryHistory reflected :=
    RootSystemReflectionClosure_result_unary vector_unary alphaCarrier betaCarrier reflectionRoute
  have wordUnary : UnaryHistory word :=
    unary_transport unary_empty (hsame_symm wordCarrier)
  have productUnary : UnaryHistory product :=
    unary_cont_closed reflectedUnary wordUnary productRoute
  exact And.intro reflectedUnary
    (And.intro productUnary
      (And.intro alphaCarrier (And.intro wordCarrier productRoute)))

theorem WeylGroupSimpleReflection_word_closure_row
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {alpha beta reflected word product : BHist}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h) :
    RootSystemFiniteSupportCarrier support Vector Nonzero alpha ->
      RootSystemFiniteSupportCarrier support Vector Nonzero beta ->
        Cont alpha beta reflected -> GroupSingletonCarrier word ->
          Cont word BHist.Empty product ->
            UnaryHistory reflected ∧ GroupSingletonCarrier product ∧ hsame product word ∧
              Cont alpha beta reflected := by
  intro alphaCarrier betaCarrier reflectionRoute wordCarrier wordProduct
  have reflectedUnary : UnaryHistory reflected :=
    RootSystemReflectionClosure_result_unary vector_unary alphaCarrier betaCarrier reflectionRoute
  have productWord : hsame product word :=
    cont_right_unit_result wordProduct
  have productCarrier : GroupSingletonCarrier product :=
    hsame_trans productWord wordCarrier
  exact And.intro reflectedUnary
    (And.intro productCarrier (And.intro productWord reflectionRoute))

def WeylGroupRootSystemGroupCarrier
    (support : ProbeBundle BHist)
    (Vector Nonzero : BHist -> Prop)
    (root word endpoint : BHist) : Prop :=
  RootSystemFiniteSupportCarrier support Vector Nonzero root ∧ GroupSingletonCarrier word ∧
    Cont root word endpoint

theorem WeylGroupRootSystemGroupCarrier_row
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {root word endpoint : BHist} :
    WeylGroupRootSystemGroupCarrier support Vector Nonzero root word endpoint ->
      RootSystemFiniteSupportCarrier support Vector Nonzero root ∧ GroupSingletonCarrier word ∧
        Cont root word endpoint ∧ hsame endpoint root := by
  intro carrier
  have sameEndpointRoot : hsame endpoint root := by
    cases carrier.right.left
    exact cont_right_unit_result carrier.right.right
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right sameEndpointRoot))

inductive WeylGroupActionTrace
    (support : ProbeBundle BHist) (Vector Nonzero : BHist -> Prop) (root : BHist) :
    List BHist -> BHist -> Prop where
  | nil :
      RootSystemFiniteSupportCarrier support Vector Nonzero root ->
        WeylGroupActionTrace support Vector Nonzero root [] root
  | cons {word endpoint product : BHist} {words : List BHist} :
      WeylGroupActionTrace support Vector Nonzero root words endpoint ->
        GroupSingletonCarrier word -> Cont endpoint word product ->
          WeylGroupActionTrace support Vector Nonzero root (word :: words) product

theorem WeylGroupActionTrace_classifier_stability_row
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root endpoint : BHist} {words : List BHist} :
    WeylGroupActionTrace support Vector Nonzero root words endpoint ->
      hsame endpoint root ∧ UnaryHistory endpoint := by
  intro trace
  induction trace with
  | nil rootCarrier =>
      exact And.intro (hsame_refl root) (vector_unary rootCarrier.right.left)
  | cons tailTrace wordCarrier step tailRows =>
      have sameProductEndpoint := by
        cases wordCarrier
        exact cont_right_unit_result step
      have sameProductRoot :=
        hsame_trans sameProductEndpoint tailRows.left
      have productUnary :=
        unary_transport tailRows.right (hsame_symm sameProductEndpoint)
      exact And.intro sameProductRoot productUnary

theorem WeylGroupCoxeterWordLedger_empty_relation_readback
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {root word relation action : BHist} :
    WeylGroupRootSystemGroupCarrier support Vector Nonzero root word action ->
      Cont word BHist.Empty relation ->
        RootSystemFiniteSupportCarrier support Vector Nonzero root ∧
          GroupSingletonCarrier relation ∧ hsame relation word ∧ hsame action root := by
  intro carrier relationReadback
  have carrierRow := WeylGroupRootSystemGroupCarrier_row carrier
  have relationWord : hsame relation word :=
    cont_right_unit_result relationReadback
  have relationCarrier : GroupSingletonCarrier relation :=
    hsame_trans relationWord carrierRow.right.left
  exact And.intro carrierRow.left
    (And.intro relationCarrier
      (And.intro relationWord carrierRow.right.right.right))

theorem WeylGroupCoxeterWordLedger_append_spine_classifier
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root wordA wordB actionA actionAB relationTail relationEndpoint : BHist} :
    WeylGroupBHistSourceRow support Vector Nonzero root wordA actionA ->
      GroupSingletonCarrier wordB ->
        Cont actionA wordB actionAB ->
          Cont actionAB relationTail relationEndpoint ->
            hsame relationTail BHist.Empty ->
              WeylGroupBHistSourceRow support Vector Nonzero root (append wordA wordB)
                  actionAB ∧
                hsame relationEndpoint root ∧ GroupSingletonCarrier relationTail := by
  intro source wordBCarrier actionStep relationStep relationTailEmpty
  have closure :
      WeylGroupBHistSourceRow support Vector Nonzero root (append wordA wordB) actionAB ∧
        hsame actionAB root ∧ GroupSingletonCarrier (append wordA wordB) :=
    WeylGroupBHistSourceRow_simple_reflection_word_closure
      vector_unary source wordBCarrier actionStep
  have endpointAction : hsame relationEndpoint actionAB := by
    cases relationTailEmpty
    exact cont_right_unit_result relationStep
  exact And.intro closure.left
    (And.intro (hsame_trans endpointAction closure.right.left) relationTailEmpty)

theorem WeylGroupRootSystemGroupCarrier_action_classifier_transport
    {support : ProbeBundle BHist}
    {Vector Nonzero : BHist -> Prop}
    {VectorClassifier : BHist -> BHist -> Prop}
    (vector_transport :
      forall {h k : BHist}, Vector h -> VectorClassifier h k -> Vector k)
    (nonzero_transport : forall {h k : BHist}, Nonzero h -> hsame h k -> Nonzero k)
    {root root' word word' endpoint endpoint' : BHist} :
    WeylGroupRootSystemGroupCarrier support Vector Nonzero root word endpoint ->
      RootSystemFiniteSupportClassifier support VectorClassifier root root' ->
        GroupSingletonClassifier word word' ->
          Cont root' word' endpoint' ->
            WeylGroupRootSystemGroupCarrier support Vector Nonzero root' word' endpoint' ∧
              hsame endpoint endpoint' := by
  intro carrier classifiedRoot classifiedWord transportedRow
  have rootCarrier :
      RootSystemFiniteSupportCarrier support Vector Nonzero root' :=
    RootSystemFiniteSupportCarrier_classifier_transport
      (support := support) (Vector := Vector) (Nonzero := Nonzero)
      (VectorClassifier := VectorClassifier) vector_transport nonzero_transport
      carrier.left classifiedRoot
  have endpointSame : hsame endpoint endpoint' :=
    cont_respects_hsame classifiedRoot.right.right.left classifiedWord.right.right
      carrier.right.right transportedRow
  exact And.intro
    (And.intro rootCarrier (And.intro classifiedWord.right.left transportedRow))
    endpointSame

theorem WeylGroupCoxeterLedger_append_spine_rows
    {support : ProbeBundle BHist} {Vector Nonzero : BHist -> Prop}
    {root wordA wordB endpointA endpointAB braid : BHist} :
    WeylGroupRootSystemGroupCarrier support Vector Nonzero root wordA endpointA ->
      GroupSingletonCarrier wordB ->
        Cont endpointA wordB endpointAB ->
          Cont wordA wordB braid ->
            WeylGroupRootSystemGroupCarrier support Vector Nonzero root braid endpointAB ∧
              GroupSingletonClassifier braid BHist.Empty ∧ hsame endpointAB root := by
  intro carrier wordBCarrier endpointStep braidStep
  have endpointARoot : hsame endpointA root := by
    cases carrier.right.left
    exact cont_right_unit_result carrier.right.right
  have endpointABEndpointA : hsame endpointAB endpointA := by
    cases wordBCarrier
    exact cont_right_unit_result endpointStep
  have endpointABRoot : hsame endpointAB root :=
    hsame_trans endpointABEndpointA endpointARoot
  have braidCarrier : GroupSingletonCarrier braid := by
    cases carrier.right.left
    cases wordBCarrier
    exact cont_deterministic braidStep (cont_right_unit BHist.Empty)
  have rootBraidEndpoint : Cont root braid endpointAB := by
    cases braidCarrier
    cases endpointABRoot
    exact cont_right_unit root
  have braidClassified : GroupSingletonClassifier braid BHist.Empty :=
    And.intro braidCarrier
      (And.intro (hsame_refl BHist.Empty) braidCarrier)
  exact And.intro
    (And.intro carrier.left (And.intro braidCarrier rootBraidEndpoint))
    (And.intro braidClassified endpointABRoot)

theorem WeylGroupPublicNameCert_export {support : ProbeBundle BHist}
    {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root word action next actionNext braid : BHist} :
    WeylGroupBHistSourceRow support Vector Nonzero root word action ->
      GroupSingletonCarrier next -> Cont action next actionNext -> Cont word next braid ->
        WeylGroupBHistSourceRow support Vector Nonzero root braid actionNext ∧
          hsame actionNext root ∧ GroupSingletonClassifier braid BHist.Empty := by
  intro source nextCarrier actionStep braidStep
  have rootUnary : UnaryHistory root :=
    vector_unary source.left.right.left
  have wordEmpty : hsame word BHist.Empty := source.right.left
  have actionSameRoot : hsame action root := by
    cases wordEmpty
    exact cont_right_unit_result source.right.right.left
  have actionNextSameAction : hsame actionNext action := by
    cases nextCarrier
    exact cont_right_unit_result actionStep
  have actionNextSameRoot : hsame actionNext root :=
    hsame_trans actionNextSameAction actionSameRoot
  have braidCarrier : GroupSingletonCarrier braid := by
    cases wordEmpty
    cases nextCarrier
    exact cont_deterministic braidStep (cont_right_unit BHist.Empty)
  have rootBraidActionNext : Cont root braid actionNext := by
    cases braidCarrier
    cases actionNextSameRoot
    exact cont_right_unit root
  have actionNextUnary : UnaryHistory actionNext :=
    unary_transport rootUnary (hsame_symm actionNextSameRoot)
  have braidClassified : GroupSingletonClassifier braid BHist.Empty :=
    And.intro braidCarrier (And.intro (hsame_refl BHist.Empty) braidCarrier)
  exact And.intro
    (And.intro source.left
      (And.intro braidCarrier (And.intro rootBraidActionNext actionNextUnary)))
    (And.intro actionNextSameRoot braidClassified)

end BEDC.Derived.WeylGroupUp
