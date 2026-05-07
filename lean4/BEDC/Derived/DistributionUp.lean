import BEDC.FKernel.Unary
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle
import BEDC.Derived.RandomVarUp
import BEDC.Derived.PreorderUp

namespace BEDC.Derived.DistributionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.FKernel.Bundle
open BEDC.Derived.RandomVarUp
open BEDC.Derived.PreorderUp

def DistributionPushforwardCarrier
    (sourcePreimage sourceMeasure : BHist -> BHist) (targetEvent pushed : BHist) : Prop :=
  Cont targetEvent BHist.Empty (sourcePreimage targetEvent) ∧
    Cont (sourcePreimage targetEvent) BHist.Empty
      (sourceMeasure (sourcePreimage targetEvent)) ∧
      hsame pushed (sourceMeasure (sourcePreimage targetEvent))

def DistributionPushforwardSourceSpec (pushed : BHist) : Prop :=
  exists sourcePreimage sourceMeasure : BHist -> BHist, exists targetEvent : BHist,
    UnaryHistory targetEvent ∧
      DistributionPushforwardCarrier sourcePreimage sourceMeasure targetEvent pushed

def DistributionPushforwardClassifier (pushed pushed' : BHist) : Prop :=
  DistributionPushforwardSourceSpec pushed ∧ DistributionPushforwardSourceSpec pushed' ∧
    hsame pushed pushed'

theorem DistributionPushforwardCarrier_row
    {sourcePreimage sourceMeasure : BHist -> BHist} {targetEvent pushed : BHist} :
    UnaryHistory targetEvent ->
      DistributionPushforwardCarrier sourcePreimage sourceMeasure targetEvent pushed ->
        UnaryHistory (sourcePreimage targetEvent) ∧
          UnaryHistory (sourceMeasure (sourcePreimage targetEvent)) ∧
            hsame pushed (sourceMeasure (sourcePreimage targetEvent)) := by
  intro targetUnary carrier
  have preimageTarget : hsame (sourcePreimage targetEvent) targetEvent :=
    cont_right_unit_result carrier.left
  have preimageUnary : UnaryHistory (sourcePreimage targetEvent) :=
    unary_transport targetUnary (hsame_symm preimageTarget)
  have measurePreimage :
      hsame (sourceMeasure (sourcePreimage targetEvent)) (sourcePreimage targetEvent) :=
    cont_right_unit_result carrier.right.left
  have measureUnary : UnaryHistory (sourceMeasure (sourcePreimage targetEvent)) :=
    unary_transport preimageUnary (hsame_symm measurePreimage)
  exact And.intro preimageUnary (And.intro measureUnary carrier.right.right)

theorem DistributionPushforwardClassifier_row
    {sourcePreimage sourceMeasure : BHist -> BHist} {targetEvent pushed pushed' : BHist} :
    UnaryHistory targetEvent ->
      DistributionPushforwardCarrier sourcePreimage sourceMeasure targetEvent pushed ->
        DistributionPushforwardCarrier sourcePreimage sourceMeasure targetEvent pushed' ->
          DistributionPushforwardClassifier pushed pushed' := by
  intro targetUnary carrier carrier'
  have pushedSource : DistributionPushforwardSourceSpec pushed :=
    Exists.intro sourcePreimage
      (Exists.intro sourceMeasure
        (Exists.intro targetEvent (And.intro targetUnary carrier)))
  have pushedSource' : DistributionPushforwardSourceSpec pushed' :=
    Exists.intro sourcePreimage
      (Exists.intro sourceMeasure
        (Exists.intro targetEvent (And.intro targetUnary carrier')))
  have samePushed : hsame pushed pushed' :=
    hsame_trans carrier.right.right (hsame_symm carrier'.right.right)
  exact And.intro pushedSource (And.intro pushedSource' samePushed)

theorem DistributionPushforwardCarrier_semantic_name_certificate :
    SemanticNameCert DistributionPushforwardSourceSpec DistributionPushforwardSourceSpec
      DistributionPushforwardSourceSpec hsame := by
  have emptyCarrier :
      DistributionPushforwardCarrier (fun h : BHist => h) (fun h : BHist => h) BHist.Empty
        BHist.Empty :=
    And.intro (cont_right_unit BHist.Empty)
      (And.intro (cont_right_unit BHist.Empty) (hsame_refl BHist.Empty))
  have emptySource : DistributionPushforwardSourceSpec BHist.Empty :=
    Exists.intro (fun h : BHist => h)
      (Exists.intro (fun h : BHist => h)
        (Exists.intro BHist.Empty (And.intro unary_empty emptyCarrier)))
  constructor
  · constructor
    · exact Exists.intro BHist.Empty emptySource
    · intro h _source
      exact hsame_refl h
    · intro h k same
      exact hsame_symm same
    · intro h k r sameHK sameKR
      exact hsame_trans sameHK sameKR
    · intro h k same source
      cases source with
      | intro sourcePreimage source =>
          cases source with
          | intro sourceMeasure source =>
              cases source with
              | intro targetEvent source =>
                  exact Exists.intro sourcePreimage
                    (Exists.intro sourceMeasure
                      (Exists.intro targetEvent
                        (And.intro source.left
                          (And.intro source.right.left
                            (And.intro source.right.right.left
                              (hsame_trans (hsame_symm same) source.right.right.right))))))
  · intro h source
    exact source
  · intro h source
    exact source

theorem DistributionPushforward_total_mass_unit
    {sourceTotal targetTotal sourceMass pushedMass unitMass : BHist} :
    UnaryHistory sourceTotal -> UnaryHistory sourceMass ->
      Cont sourceTotal BHist.Empty targetTotal -> hsame sourceMass sourceTotal ->
        hsame pushedMass targetTotal -> hsame sourceMass unitMass ->
          UnaryHistory pushedMass ∧ hsame pushedMass unitMass := by
  intro _sourceTotalUnary sourceMassUnary totalReadback sourceMassTotal pushedMassTarget
  intro sourceMassUnit
  have targetSource : hsame targetTotal sourceTotal :=
    cont_right_unit_result totalReadback
  have pushedSource : hsame pushedMass sourceTotal :=
    hsame_trans pushedMassTarget targetSource
  have pushedSourceMass : hsame pushedMass sourceMass :=
    hsame_trans pushedSource (hsame_symm sourceMassTotal)
  have pushedUnit : hsame pushedMass unitMass :=
    hsame_trans pushedSourceMass sourceMassUnit
  exact And.intro (unary_transport sourceMassUnary (hsame_symm pushedSourceMass)) pushedUnit

theorem DistributionPushforwardWitness_total_mass_unit
    {targetTotal sourceTotal chosenPreimage sourceTotalMass pushedTotal probabilityUnit : BHist} :
    BEDC.Derived.RandomVarUp.RandomVarTotalReadbackCertificate targetTotal sourceTotal
      chosenPreimage ->
      Cont sourceTotal BHist.Empty sourceTotalMass ->
        hsame pushedTotal sourceTotalMass ->
          hsame sourceTotalMass probabilityUnit ->
            hsame pushedTotal probabilityUnit ∧ hsame chosenPreimage sourceTotal := by
  intro randomVarCert sourceTotalMassReadback pushedSourceMass sourceMassUnit
  have chosenSourceTotal : hsame chosenPreimage sourceTotal :=
    cont_deterministic randomVarCert.chosen_readback randomVarCert.carried_total_bridge
  have sourceMassSource : hsame sourceTotalMass sourceTotal :=
    cont_deterministic sourceTotalMassReadback (cont_right_unit sourceTotal)
  have chosenSourceMass : hsame chosenPreimage sourceTotalMass :=
    hsame_trans chosenSourceTotal (hsame_symm sourceMassSource)
  exact And.intro (hsame_trans pushedSourceMass sourceMassUnit)
    (hsame_trans chosenSourceMass sourceMassSource)

theorem DistributionPushforward_row
    {targetEvent sourcePreimage sourceValue pushedValue : BHist} :
    Cont targetEvent BHist.Empty sourcePreimage ->
      Cont sourcePreimage BHist.Empty sourceValue ->
        hsame pushedValue sourceValue ->
          hsame sourcePreimage targetEvent ∧
            hsame sourceValue sourcePreimage ∧ hsame pushedValue targetEvent := by
  intro preimageRow sourceValueRow pushedSourceValue
  have preimageTarget : hsame sourcePreimage targetEvent :=
    cont_right_unit_result preimageRow
  have sourceValuePreimage : hsame sourceValue sourcePreimage :=
    cont_right_unit_result sourceValueRow
  have pushedTarget : hsame pushedValue targetEvent :=
    hsame_trans pushedSourceValue (hsame_trans sourceValuePreimage preimageTarget)
  exact And.intro preimageTarget (And.intro sourceValuePreimage pushedTarget)

theorem DistributionPushforward_empty_target_event_zero_mass
    {targetEmpty sourceEmpty sourceValue pushValue : BHist} :
    hsame targetEmpty BHist.Empty -> hsame sourceEmpty BHist.Empty ->
      Cont sourceEmpty BHist.Empty sourceValue -> Cont targetEmpty sourceValue pushValue ->
        hsame pushValue BHist.Empty := by
  intro targetEmptyZero sourceEmptyZero sourceEndpoint pushEndpoint
  have sourceValueZero : hsame sourceValue BHist.Empty :=
    cont_respects_hsame sourceEmptyZero (hsame_refl BHist.Empty)
      sourceEndpoint (cont_left_unit BHist.Empty)
  have pushValueZero : hsame pushValue BHist.Empty :=
    cont_respects_hsame targetEmptyZero sourceValueZero pushEndpoint
      (cont_left_unit BHist.Empty)
  exact pushValueZero

theorem DistributionPushforward_finite_disjoint_union_additivity
    {sourceB sourceC sourceU pushedB pushedC pushedU pushedSum : BHist} :
    Cont sourceB sourceC sourceU -> hsame pushedU sourceU -> hsame pushedB sourceB ->
      hsame pushedC sourceC -> Cont pushedB pushedC pushedSum -> hsame pushedU pushedSum := by
  intro sourceUnion pushedUnionSource pushedBSource pushedCSource pushedUnion
  have sourcePushedUnion : hsame sourceU pushedSum :=
    cont_respects_hsame (hsame_symm pushedBSource) (hsame_symm pushedCSource)
      sourceUnion pushedUnion
  exact hsame_trans pushedUnionSource sourcePushedUnion

theorem DistributionPushforward_relative_difference_additivity
    {sourceB sourceD sourceA pushB pushD pushA pushSum : BHist} :
    Cont sourceB sourceD sourceA -> hsame pushA sourceA -> hsame pushB sourceB ->
      hsame pushD sourceD -> Cont pushB pushD pushSum -> hsame pushA pushSum := by
  intro sourceSum pushAClass pushBClass pushDClass pushSumCont
  have sourcePushSum : hsame sourceA pushSum :=
    cont_respects_hsame (hsame_symm pushBClass) (hsame_symm pushDClass) sourceSum pushSumCont
  exact hsame_trans pushAClass sourcePushSum

theorem DistributionPushforward_complement_mass_decomposition
    {targetTotal event complement pushedTotal pushedEvent pushedComplement pushedSum
      probabilityUnit : BHist} :
    Cont event complement targetTotal -> hsame pushedEvent event ->
      hsame pushedComplement complement -> Cont pushedEvent pushedComplement pushedSum ->
        hsame pushedTotal targetTotal -> hsame pushedTotal probabilityUnit ->
          hsame pushedTotal pushedSum ∧ hsame probabilityUnit pushedSum := by
  intro targetComplement pushedEventEvent pushedComplementComplement pushedComplementRow
  intro pushedTotalTarget pushedTotalUnit
  have targetPushedSum : hsame targetTotal pushedSum :=
    cont_respects_hsame (hsame_symm pushedEventEvent)
      (hsame_symm pushedComplementComplement) targetComplement pushedComplementRow
  have pushedTotalPushedSum : hsame pushedTotal pushedSum :=
    hsame_trans pushedTotalTarget targetPushedSum
  exact And.intro pushedTotalPushedSum (hsame_trans (hsame_symm pushedTotalUnit)
    pushedTotalPushedSum)

theorem DistributionPushforward_monotone_under_target_inclusion
    {sourceB sourceD sourceA pushB pushD pushA pushSum : BHist} :
    Cont sourceB sourceD sourceA -> hsame pushA sourceA -> hsame pushB sourceB ->
      hsame pushD sourceD -> Cont pushB pushD pushSum -> UnaryHistory pushD ->
        exists witness : BHist, Cont pushB witness pushA ∧ UnaryHistory witness := by
  intro sourceSum pushAClass pushBClass pushDClass pushSumCont pushDUnary
  have pushAFromSum : hsame pushA pushSum :=
    DistributionPushforward_relative_difference_additivity sourceSum pushAClass pushBClass
      pushDClass pushSumCont
  have pushDToPushA : Cont pushB pushD pushA :=
    cont_result_hsame_transport pushSumCont (hsame_symm pushAFromSum)
  exact Exists.intro pushD (And.intro pushDToPushA pushDUnary)

theorem DistributionPushforward_monotone_events
    {sourceB sourceD sourceA pushB pushD pushA pushSum : BHist} :
    UnaryHistory sourceB -> UnaryHistory pushD -> Cont sourceB sourceD sourceA ->
      hsame pushA sourceA -> hsame pushB sourceB -> hsame pushD sourceD ->
        Cont pushB pushD pushSum -> UnaryHistory pushB ∧ PreorderPrefixLE pushB pushA := by
  intro sourceBUnary pushDUnary sourceSum pushAClass pushBClass pushDClass pushSumCont
  have pushBUnary : UnaryHistory pushB :=
    unary_transport sourceBUnary (hsame_symm pushBClass)
  have pushAFromSum : hsame pushA pushSum :=
    DistributionPushforward_relative_difference_additivity sourceSum pushAClass pushBClass
      pushDClass pushSumCont
  have pushDToPushA : Cont pushB pushD pushA :=
    cont_result_hsame_transport pushSumCont (hsame_symm pushAFromSum)
  exact And.intro pushBUnary (Exists.intro pushD (And.intro pushDUnary pushDToPushA))

theorem DistributionPushforward_probability_bounds
    {event gap sourceTotal sourceTotalMass pushedEvent pushedTotal probabilityUnit pushedSum :
      BHist} :
    UnaryHistory event -> UnaryHistory gap -> Cont event gap sourceTotal ->
      Cont sourceTotal BHist.Empty sourceTotalMass -> hsame pushedEvent event ->
        hsame pushedTotal sourceTotalMass -> hsame sourceTotalMass probabilityUnit ->
          Cont pushedEvent gap pushedSum -> hsame pushedTotal pushedSum ->
            UnaryHistory pushedEvent ∧ PreorderPrefixLE pushedEvent probabilityUnit := by
  intro eventUnary gapUnary eventGap sourceMassReadback pushedEventEvent pushedTotalMass
  intro sourceMassUnit pushedSumCont pushedTotalSum
  have pushedEventUnary : UnaryHistory pushedEvent :=
    unary_transport eventUnary (hsame_symm pushedEventEvent)
  have sourceTotalUnary : UnaryHistory sourceTotal :=
    unary_cont_closed eventUnary gapUnary eventGap
  have sourceMassUnary : UnaryHistory sourceTotalMass :=
    unary_transport sourceTotalUnary (hsame_symm (cont_right_unit_result sourceMassReadback))
  have pushedTotalUnary : UnaryHistory pushedTotal :=
    unary_transport sourceMassUnary (hsame_symm pushedTotalMass)
  have pushedSumUnit : hsame pushedSum probabilityUnit :=
    hsame_trans (hsame_symm pushedTotalSum) (hsame_trans pushedTotalMass sourceMassUnit)
  have pushedSumUnitCont : Cont pushedEvent gap probabilityUnit :=
    cont_result_hsame_transport pushedSumCont pushedSumUnit
  exact And.intro pushedEventUnary
    (Exists.intro gap (And.intro gapUnary pushedSumUnitCont))

theorem DistributionPushforward_probability_package
    {sourceTotal targetTotal sourceMass pushedMass unitMass targetEmpty sourceEmpty sourceValue
      pushEmpty event gap probabilityUnit pushedEvent pushedTotal pushedSum : BHist} :
    UnaryHistory sourceTotal -> UnaryHistory sourceMass ->
      Cont sourceTotal BHist.Empty targetTotal -> hsame sourceMass sourceTotal ->
        hsame pushedMass targetTotal -> hsame sourceMass unitMass ->
          hsame targetEmpty BHist.Empty -> hsame sourceEmpty BHist.Empty ->
            Cont sourceEmpty BHist.Empty sourceValue ->
              Cont targetEmpty sourceValue pushEmpty -> UnaryHistory event ->
                UnaryHistory gap -> Cont event gap sourceTotal ->
                  Cont sourceTotal BHist.Empty sourceMass -> hsame pushedEvent event ->
                    hsame pushedTotal sourceMass -> hsame sourceMass probabilityUnit ->
                      Cont pushedEvent gap pushedSum -> hsame pushedTotal pushedSum ->
                        (UnaryHistory pushedMass ∧ hsame pushedMass unitMass) ∧
                          hsame pushEmpty BHist.Empty ∧
                            UnaryHistory pushedEvent ∧
                              PreorderPrefixLE pushedEvent probabilityUnit := by
  intro sourceTotalUnary sourceMassUnary totalReadback sourceMassTotal pushedMassTarget
  intro sourceMassUnit targetEmptyZero sourceEmptyZero sourceEmptyReadback pushEmptyReadback
  intro eventUnary gapUnary eventGap sourceMassReadback pushedEventEvent pushedTotalMass
  intro sourceMassProbabilityUnit pushedSumCont pushedTotalSum
  have totalMassUnit :
      UnaryHistory pushedMass ∧ hsame pushedMass unitMass :=
    DistributionPushforward_total_mass_unit sourceTotalUnary sourceMassUnary totalReadback
      sourceMassTotal pushedMassTarget sourceMassUnit
  have emptyMassZero : hsame pushEmpty BHist.Empty :=
    DistributionPushforward_empty_target_event_zero_mass targetEmptyZero sourceEmptyZero
      sourceEmptyReadback pushEmptyReadback
  have probabilityBounds :
      UnaryHistory pushedEvent ∧ PreorderPrefixLE pushedEvent probabilityUnit :=
    DistributionPushforward_probability_bounds eventUnary gapUnary eventGap sourceMassReadback
      pushedEventEvent pushedTotalMass sourceMassProbabilityUnit pushedSumCont pushedTotalSum
  exact And.intro totalMassUnit (And.intro emptyMassZero probabilityBounds)

theorem DistributionPushforward_nonnegative_value_inheritance
    {sourceValue pushedValue witness : BHist} :
    UnaryHistory sourceValue -> Cont sourceValue BHist.Empty witness ->
      hsame pushedValue witness -> UnaryHistory pushedValue ∧ hsame pushedValue sourceValue := by
  intro sourceNonnegative sourceReadback pushedWitness
  have witnessSource : hsame witness sourceValue :=
    cont_right_unit_result sourceReadback
  have pushedSource : hsame pushedValue sourceValue :=
    hsame_trans pushedWitness witnessSource
  exact And.intro (unary_transport sourceNonnegative (hsame_symm pushedSource)) pushedSource

def DistributionPushforwardMassFold : ProbeBundle BHist -> BHist
  | ProbeBundle.Bnil => BHist.Empty
  | ProbeBundle.Bcons x xs => append x (DistributionPushforwardMassFold xs)

theorem DistributionPushforward_countable_disjoint_sigma_additivity
    (left right : ProbeBundle BHist) :
    hsame (DistributionPushforwardMassFold (bundleAppend left right))
      (append (DistributionPushforwardMassFold left) (DistributionPushforwardMassFold right)) := by
  induction left with
  | Bnil =>
      exact (append_empty_left (DistributionPushforwardMassFold right)).symm
  | Bcons x xs ih =>
      exact (congrArg (append x) ih).trans
        (append_assoc x (DistributionPushforwardMassFold xs)
          (DistributionPushforwardMassFold right)).symm

def DistributionPushforwardLayerPrefix (layers : Nat -> BHist) : Nat -> BHist
  | Nat.zero => layers Nat.zero
  | Nat.succ n => append (DistributionPushforwardLayerPrefix layers n) (layers (Nat.succ n))

theorem DistributionPushforward_continuity_from_below_prefix_readback
    {layers targetValues : Nat -> BHist} :
    (forall n : Nat, UnaryHistory (layers n)) ->
      (forall n : Nat, hsame (targetValues n) (DistributionPushforwardLayerPrefix layers n)) ->
        forall n : Nat,
          UnaryHistory (DistributionPushforwardLayerPrefix layers n) ∧
            hsame (targetValues n) (DistributionPushforwardLayerPrefix layers n) ∧
              PreorderPrefixLE (targetValues n) (targetValues (Nat.succ n)) := by
  intro layersUnary targetReadback n
  induction n with
  | zero =>
      have prefixUnary :
          UnaryHistory (DistributionPushforwardLayerPrefix layers Nat.zero) :=
        layersUnary Nat.zero
      have currentReadback :
          hsame (targetValues Nat.zero)
            (DistributionPushforwardLayerPrefix layers Nat.zero) :=
        targetReadback Nat.zero
      have nextReadback :
          hsame (targetValues (Nat.succ Nat.zero))
            (DistributionPushforwardLayerPrefix layers (Nat.succ Nat.zero)) :=
        targetReadback (Nat.succ Nat.zero)
      have nextStep :
          Cont (DistributionPushforwardLayerPrefix layers Nat.zero)
            (layers (Nat.succ Nat.zero))
            (DistributionPushforwardLayerPrefix layers (Nat.succ Nat.zero)) :=
        cont_intro rfl
      have prefixLE :
          PreorderPrefixLE (targetValues Nat.zero) (targetValues (Nat.succ Nat.zero)) :=
        Exists.intro (layers (Nat.succ Nat.zero))
          (And.intro (layersUnary (Nat.succ Nat.zero))
            (cont_hsame_transport (hsame_symm currentReadback)
              (hsame_refl (layers (Nat.succ Nat.zero))) (hsame_symm nextReadback) nextStep))
      exact And.intro prefixUnary (And.intro currentReadback prefixLE)
  | succ n ih =>
      have prefixUnary :
          UnaryHistory (DistributionPushforwardLayerPrefix layers (Nat.succ n)) :=
        unary_append_closed ih.left (layersUnary (Nat.succ n))
      have currentReadback :
          hsame (targetValues (Nat.succ n))
            (DistributionPushforwardLayerPrefix layers (Nat.succ n)) :=
        targetReadback (Nat.succ n)
      have nextReadback :
          hsame (targetValues (Nat.succ (Nat.succ n)))
            (DistributionPushforwardLayerPrefix layers (Nat.succ (Nat.succ n))) :=
        targetReadback (Nat.succ (Nat.succ n))
      have nextStep :
          Cont (DistributionPushforwardLayerPrefix layers (Nat.succ n))
            (layers (Nat.succ (Nat.succ n)))
            (DistributionPushforwardLayerPrefix layers (Nat.succ (Nat.succ n))) :=
        cont_intro rfl
      have prefixLE :
          PreorderPrefixLE (targetValues (Nat.succ n))
            (targetValues (Nat.succ (Nat.succ n))) :=
        Exists.intro (layers (Nat.succ (Nat.succ n)))
          (And.intro (layersUnary (Nat.succ (Nat.succ n)))
            (cont_hsame_transport (hsame_symm currentReadback)
              (hsame_refl (layers (Nat.succ (Nat.succ n)))) (hsame_symm nextReadback)
              nextStep))
      exact And.intro prefixUnary (And.intro currentReadback prefixLE)

end BEDC.Derived.DistributionUp
