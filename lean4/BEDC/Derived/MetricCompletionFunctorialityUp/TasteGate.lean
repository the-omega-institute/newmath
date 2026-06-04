import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetricCompletionFunctorialityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetricCompletionFunctorialityUp : Type where
  | mk
      (source target graph cauchyControl completionEntry universalProperty comparison
        transport replay provenance localName : BHist) :
      MetricCompletionFunctorialityUp
  deriving DecidableEq

def metricCompletionFunctorialityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metricCompletionFunctorialityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metricCompletionFunctorialityEncodeBHist h

def metricCompletionFunctorialityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metricCompletionFunctorialityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metricCompletionFunctorialityDecodeBHist tail)

private theorem metricCompletionFunctoriality_decode_encode_bhist :
    ∀ h : BHist,
      metricCompletionFunctorialityDecodeBHist
          (metricCompletionFunctorialityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem metricCompletionFunctorialityEncodeBHist_injective {h k : BHist} :
    metricCompletionFunctorialityEncodeBHist h =
        metricCompletionFunctorialityEncodeBHist k →
      h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      metricCompletionFunctorialityDecodeBHist
          (metricCompletionFunctorialityEncodeBHist h) =
        metricCompletionFunctorialityDecodeBHist
          (metricCompletionFunctorialityEncodeBHist k) :=
    congrArg metricCompletionFunctorialityDecodeBHist heq
  exact
    Eq.trans (metricCompletionFunctoriality_decode_encode_bhist h).symm
      (Eq.trans hdecode (metricCompletionFunctoriality_decode_encode_bhist k))

private theorem metricCompletionFunctoriality_mk_congr
    {source source' target target' graph graph' cauchyControl cauchyControl'
      completionEntry completionEntry' universalProperty universalProperty'
      comparison comparison' transport transport' replay replay' provenance provenance'
      localName localName' : BHist}
    (hSource : source' = source)
    (hTarget : target' = target)
    (hGraph : graph' = graph)
    (hControl : cauchyControl' = cauchyControl)
    (hEntry : completionEntry' = completionEntry)
    (hUniversal : universalProperty' = universalProperty)
    (hComparison : comparison' = comparison)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    MetricCompletionFunctorialityUp.mk source' target' graph' cauchyControl'
        completionEntry' universalProperty' comparison' transport' replay' provenance'
        localName' =
      MetricCompletionFunctorialityUp.mk source target graph cauchyControl completionEntry
        universalProperty comparison transport replay provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hSource
  cases hTarget
  cases hGraph
  cases hControl
  cases hEntry
  cases hUniversal
  cases hComparison
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hLocalName
  rfl

def metricCompletionFunctorialityToEventFlow :
    MetricCompletionFunctorialityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetricCompletionFunctorialityUp.mk source target graph cauchyControl completionEntry
      universalProperty comparison transport replay provenance localName =>
      [[BMark.b0],
        metricCompletionFunctorialityEncodeBHist source,
        metricCompletionFunctorialityEncodeBHist target,
        metricCompletionFunctorialityEncodeBHist graph,
        metricCompletionFunctorialityEncodeBHist cauchyControl,
        metricCompletionFunctorialityEncodeBHist completionEntry,
        metricCompletionFunctorialityEncodeBHist universalProperty,
        metricCompletionFunctorialityEncodeBHist comparison,
        metricCompletionFunctorialityEncodeBHist transport,
        metricCompletionFunctorialityEncodeBHist replay,
        metricCompletionFunctorialityEncodeBHist provenance,
        metricCompletionFunctorialityEncodeBHist localName]

def metricCompletionFunctorialityFromEventFlow :
    EventFlow → Option MetricCompletionFunctorialityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest =>
      match rest with
      | [] => none
      | source :: rest =>
          match rest with
          | [] => none
          | target :: rest =>
              match rest with
              | [] => none
              | graph :: rest =>
                  match rest with
                  | [] => none
                  | cauchyControl :: rest =>
                      match rest with
                      | [] => none
                      | completionEntry :: rest =>
                          match rest with
                          | [] => none
                          | universalProperty :: rest =>
                              match rest with
                              | [] => none
                              | comparison :: rest =>
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
                                                        (MetricCompletionFunctorialityUp.mk
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            source)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            target)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            graph)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            cauchyControl)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            completionEntry)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            universalProperty)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            comparison)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            transport)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            replay)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            provenance)
                                                          (metricCompletionFunctorialityDecodeBHist
                                                            localName))
                                                  | _ :: _ => none

private theorem metricCompletionFunctoriality_round_trip :
    ∀ x : MetricCompletionFunctorialityUp,
      metricCompletionFunctorialityFromEventFlow
        (metricCompletionFunctorialityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target graph cauchyControl completionEntry universalProperty comparison
      transport replay provenance localName =>
      change
        some
          (MetricCompletionFunctorialityUp.mk
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist source))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist target))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist graph))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist cauchyControl))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist completionEntry))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist universalProperty))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist comparison))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist transport))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist replay))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist provenance))
            (metricCompletionFunctorialityDecodeBHist
              (metricCompletionFunctorialityEncodeBHist localName))) =
          some
            (MetricCompletionFunctorialityUp.mk source target graph cauchyControl
              completionEntry universalProperty comparison transport replay provenance
              localName)
      exact
        congrArg some
          (metricCompletionFunctoriality_mk_congr
            (metricCompletionFunctoriality_decode_encode_bhist source)
            (metricCompletionFunctoriality_decode_encode_bhist target)
            (metricCompletionFunctoriality_decode_encode_bhist graph)
            (metricCompletionFunctoriality_decode_encode_bhist cauchyControl)
            (metricCompletionFunctoriality_decode_encode_bhist completionEntry)
            (metricCompletionFunctoriality_decode_encode_bhist universalProperty)
            (metricCompletionFunctoriality_decode_encode_bhist comparison)
            (metricCompletionFunctoriality_decode_encode_bhist transport)
            (metricCompletionFunctoriality_decode_encode_bhist replay)
            (metricCompletionFunctoriality_decode_encode_bhist provenance)
            (metricCompletionFunctoriality_decode_encode_bhist localName))

private theorem metricCompletionFunctorialityToEventFlow_injective
    {x y : MetricCompletionFunctorialityUp} :
    metricCompletionFunctorialityToEventFlow x =
        metricCompletionFunctorialityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk source target graph cauchyControl completionEntry universalProperty comparison
      transport replay provenance localName =>
      cases y with
      | mk source' target' graph' cauchyControl' completionEntry' universalProperty'
          comparison' transport' replay' provenance' localName' =>
          injection heq with _tagEq tailEq0
          injection tailEq0 with sourceEq tailEq1
          injection tailEq1 with targetEq tailEq2
          injection tailEq2 with graphEq tailEq3
          injection tailEq3 with controlEq tailEq4
          injection tailEq4 with entryEq tailEq5
          injection tailEq5 with universalEq tailEq6
          injection tailEq6 with comparisonEq tailEq7
          injection tailEq7 with transportEq tailEq8
          injection tailEq8 with replayEq tailEq9
          injection tailEq9 with provenanceEq tailEq10
          injection tailEq10 with localNameEq _nilEq
          exact
            metricCompletionFunctoriality_mk_congr
              (metricCompletionFunctorialityEncodeBHist_injective sourceEq)
              (metricCompletionFunctorialityEncodeBHist_injective targetEq)
              (metricCompletionFunctorialityEncodeBHist_injective graphEq)
              (metricCompletionFunctorialityEncodeBHist_injective controlEq)
              (metricCompletionFunctorialityEncodeBHist_injective entryEq)
              (metricCompletionFunctorialityEncodeBHist_injective universalEq)
              (metricCompletionFunctorialityEncodeBHist_injective comparisonEq)
              (metricCompletionFunctorialityEncodeBHist_injective transportEq)
              (metricCompletionFunctorialityEncodeBHist_injective replayEq)
              (metricCompletionFunctorialityEncodeBHist_injective provenanceEq)
              (metricCompletionFunctorialityEncodeBHist_injective localNameEq)

instance metricCompletionFunctorialityBHistCarrier :
    BHistCarrier MetricCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metricCompletionFunctorialityToEventFlow
  fromEventFlow := metricCompletionFunctorialityFromEventFlow

instance metricCompletionFunctorialityChapterTasteGate :
    ChapterTasteGate MetricCompletionFunctorialityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metricCompletionFunctorialityFromEventFlow
        (metricCompletionFunctorialityToEventFlow x) = some x
    exact metricCompletionFunctoriality_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metricCompletionFunctorialityToEventFlow_injective heq)

theorem MetricCompletionFunctorialityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metricCompletionFunctorialityDecodeBHist
        (metricCompletionFunctorialityEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetricCompletionFunctorialityUp) ∧
        Nonempty (ChapterTasteGate MetricCompletionFunctorialityUp) ∧
          metricCompletionFunctorialityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨metricCompletionFunctoriality_decode_encode_bhist,
      ⟨metricCompletionFunctorialityBHistCarrier⟩,
      ⟨metricCompletionFunctorialityChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MetricCompletionFunctorialityUp
