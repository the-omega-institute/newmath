import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DistributionDerivativeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DistributionDerivativeUp : Type where
  | mk
      (testAction inputDistribution signHandoff candidateAction sharedReadback streamWindows
        transport replay provenance localName : BHist) :
      DistributionDerivativeUp
  deriving DecidableEq

def distributionDerivativeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: distributionDerivativeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: distributionDerivativeEncodeBHist h

def distributionDerivativeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (distributionDerivativeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (distributionDerivativeDecodeBHist tail)

private theorem distributionDerivative_decode_encode_bhist :
    ∀ h : BHist, distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem distributionDerivativeEncodeBHist_injective {h k : BHist} :
    distributionDerivativeEncodeBHist h = distributionDerivativeEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist h) =
        distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist k) :=
    congrArg distributionDerivativeDecodeBHist heq
  exact
    Eq.trans (distributionDerivative_decode_encode_bhist h).symm
      (Eq.trans hdecode (distributionDerivative_decode_encode_bhist k))

private theorem distributionDerivative_mk_congr
    {testAction testAction' inputDistribution inputDistribution' signHandoff signHandoff'
      candidateAction candidateAction' sharedReadback sharedReadback' streamWindows
      streamWindows' transport transport' replay replay' provenance provenance' localName
      localName' : BHist}
    (hTestAction : testAction' = testAction)
    (hInputDistribution : inputDistribution' = inputDistribution)
    (hSignHandoff : signHandoff' = signHandoff)
    (hCandidateAction : candidateAction' = candidateAction)
    (hSharedReadback : sharedReadback' = sharedReadback)
    (hStreamWindows : streamWindows' = streamWindows)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    DistributionDerivativeUp.mk testAction' inputDistribution' signHandoff' candidateAction'
        sharedReadback' streamWindows' transport' replay' provenance' localName' =
      DistributionDerivativeUp.mk testAction inputDistribution signHandoff candidateAction
        sharedReadback streamWindows transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTestAction
  cases hInputDistribution
  cases hSignHandoff
  cases hCandidateAction
  cases hSharedReadback
  cases hStreamWindows
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def distributionDerivativeToEventFlow : DistributionDerivativeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DistributionDerivativeUp.mk testAction inputDistribution signHandoff candidateAction
      sharedReadback streamWindows transport replay provenance localName =>
      [[BMark.b0],
        distributionDerivativeEncodeBHist testAction,
        distributionDerivativeEncodeBHist inputDistribution,
        distributionDerivativeEncodeBHist signHandoff,
        distributionDerivativeEncodeBHist candidateAction,
        distributionDerivativeEncodeBHist sharedReadback,
        distributionDerivativeEncodeBHist streamWindows,
        distributionDerivativeEncodeBHist transport,
        distributionDerivativeEncodeBHist replay,
        distributionDerivativeEncodeBHist provenance,
        distributionDerivativeEncodeBHist localName]

def distributionDerivativeFromEventFlow : EventFlow → Option DistributionDerivativeUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest =>
      match rest with
      | [] => none
      | testAction :: rest =>
          match rest with
          | [] => none
          | inputDistribution :: rest =>
              match rest with
              | [] => none
              | signHandoff :: rest =>
                  match rest with
                  | [] => none
                  | candidateAction :: rest =>
                      match rest with
                      | [] => none
                      | sharedReadback :: rest =>
                          match rest with
                          | [] => none
                          | streamWindows :: rest =>
                              match rest with
                              | [] => none
                              | transport :: rest =>
                                  match rest with
                                  | [] => none
                                  | replay :: rest =>
                                      match rest with
                                      | [] => none
                                      | provenance :: rest =>
                                          match rest with
                                          | [] => none
                                          | localName :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (DistributionDerivativeUp.mk
                                                      (distributionDerivativeDecodeBHist
                                                        testAction)
                                                      (distributionDerivativeDecodeBHist
                                                        inputDistribution)
                                                      (distributionDerivativeDecodeBHist
                                                        signHandoff)
                                                      (distributionDerivativeDecodeBHist
                                                        candidateAction)
                                                      (distributionDerivativeDecodeBHist
                                                        sharedReadback)
                                                      (distributionDerivativeDecodeBHist
                                                        streamWindows)
                                                      (distributionDerivativeDecodeBHist
                                                        transport)
                                                      (distributionDerivativeDecodeBHist replay)
                                                      (distributionDerivativeDecodeBHist
                                                        provenance)
                                                      (distributionDerivativeDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem distributionDerivative_round_trip :
    ∀ x : DistributionDerivativeUp,
      distributionDerivativeFromEventFlow (distributionDerivativeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk testAction inputDistribution signHandoff candidateAction sharedReadback streamWindows
      transport replay provenance localName =>
      change
        some
          (DistributionDerivativeUp.mk
            (distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist testAction))
            (distributionDerivativeDecodeBHist
              (distributionDerivativeEncodeBHist inputDistribution))
            (distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist signHandoff))
            (distributionDerivativeDecodeBHist
              (distributionDerivativeEncodeBHist candidateAction))
            (distributionDerivativeDecodeBHist
              (distributionDerivativeEncodeBHist sharedReadback))
            (distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist streamWindows))
            (distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist transport))
            (distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist replay))
            (distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist provenance))
            (distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist localName))) =
          some
            (DistributionDerivativeUp.mk testAction inputDistribution signHandoff candidateAction
              sharedReadback streamWindows transport replay provenance localName)
      exact
        congrArg some
          (distributionDerivative_mk_congr
            (distributionDerivative_decode_encode_bhist testAction)
            (distributionDerivative_decode_encode_bhist inputDistribution)
            (distributionDerivative_decode_encode_bhist signHandoff)
            (distributionDerivative_decode_encode_bhist candidateAction)
            (distributionDerivative_decode_encode_bhist sharedReadback)
            (distributionDerivative_decode_encode_bhist streamWindows)
            (distributionDerivative_decode_encode_bhist transport)
            (distributionDerivative_decode_encode_bhist replay)
            (distributionDerivative_decode_encode_bhist provenance)
            (distributionDerivative_decode_encode_bhist localName))

private theorem distributionDerivativeToEventFlow_injective {x y : DistributionDerivativeUp} :
    distributionDerivativeToEventFlow x = distributionDerivativeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk testAction inputDistribution signHandoff candidateAction sharedReadback streamWindows
      transport replay provenance localName =>
      cases y with
      | mk testAction' inputDistribution' signHandoff' candidateAction' sharedReadback'
          streamWindows' transport' replay' provenance' localName' =>
          injection heq with _tagEq tailEq0
          injection tailEq0 with testActionEq tailEq1
          injection tailEq1 with inputDistributionEq tailEq2
          injection tailEq2 with signHandoffEq tailEq3
          injection tailEq3 with candidateActionEq tailEq4
          injection tailEq4 with sharedReadbackEq tailEq5
          injection tailEq5 with streamWindowsEq tailEq6
          injection tailEq6 with transportEq tailEq7
          injection tailEq7 with replayEq tailEq8
          injection tailEq8 with provenanceEq tailEq9
          injection tailEq9 with localNameEq _nilEq
          exact
            distributionDerivative_mk_congr
              (distributionDerivativeEncodeBHist_injective testActionEq)
              (distributionDerivativeEncodeBHist_injective inputDistributionEq)
              (distributionDerivativeEncodeBHist_injective signHandoffEq)
              (distributionDerivativeEncodeBHist_injective candidateActionEq)
              (distributionDerivativeEncodeBHist_injective sharedReadbackEq)
              (distributionDerivativeEncodeBHist_injective streamWindowsEq)
              (distributionDerivativeEncodeBHist_injective transportEq)
              (distributionDerivativeEncodeBHist_injective replayEq)
              (distributionDerivativeEncodeBHist_injective provenanceEq)
              (distributionDerivativeEncodeBHist_injective localNameEq)

instance distributionDerivativeBHistCarrier : BHistCarrier DistributionDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := distributionDerivativeToEventFlow
  fromEventFlow := distributionDerivativeFromEventFlow

instance distributionDerivativeChapterTasteGate : ChapterTasteGate DistributionDerivativeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change distributionDerivativeFromEventFlow (distributionDerivativeToEventFlow x) = some x
    exact distributionDerivative_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (distributionDerivativeToEventFlow_injective heq)

theorem DistributionDerivativeTasteGate_single_carrier_alignment :
    (∀ h : BHist, distributionDerivativeDecodeBHist (distributionDerivativeEncodeBHist h) = h) ∧
      (∀ x : DistributionDerivativeUp,
        distributionDerivativeFromEventFlow (distributionDerivativeToEventFlow x) = some x) ∧
        (∀ x y : DistributionDerivativeUp,
          distributionDerivativeToEventFlow x = distributionDerivativeToEventFlow y → x = y) ∧
          distributionDerivativeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    exact distributionDerivative_decode_encode_bhist h
  · constructor
    · intro x
      exact distributionDerivative_round_trip x
    · constructor
      · intro x y heq
        exact distributionDerivativeToEventFlow_injective heq
      · rfl

end BEDC.Derived.DistributionDerivativeUp
