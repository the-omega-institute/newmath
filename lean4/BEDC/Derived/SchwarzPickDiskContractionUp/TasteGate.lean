import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SchwarzPickDiskContractionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SchwarzPickDiskContractionUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk :
      (disk map metric contraction boundary route transport replay provenance nameCert : BHist) ->
        SchwarzPickDiskContractionUp
  deriving DecidableEq

def schwarzPickDiskContractionEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: schwarzPickDiskContractionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: schwarzPickDiskContractionEncodeBHist h

def schwarzPickDiskContractionDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (schwarzPickDiskContractionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (schwarzPickDiskContractionDecodeBHist tail)

private theorem SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      schwarzPickDiskContractionDecodeBHist (schwarzPickDiskContractionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def schwarzPickDiskContractionFields :
    SchwarzPickDiskContractionUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SchwarzPickDiskContractionUp.mk disk map metric contraction boundary route transport replay
      provenance nameCert =>
        [disk, map, metric, contraction, boundary, route, transport, replay, provenance, nameCert]

def schwarzPickDiskContractionToEventFlow :
    SchwarzPickDiskContractionUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => schwarzPickDiskContractionFields x |>.map schwarzPickDiskContractionEncodeBHist

def schwarzPickDiskContractionFromEventFlow :
    EventFlow -> Option SchwarzPickDiskContractionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | disk :: rest1 =>
      match rest1 with
      | [] => none
      | map :: rest2 =>
          match rest2 with
          | [] => none
          | metric :: rest3 =>
              match rest3 with
              | [] => none
              | contraction :: rest4 =>
                  match rest4 with
                  | [] => none
                  | boundary :: rest5 =>
                      match rest5 with
                      | [] => none
                      | route :: rest6 =>
                          match rest6 with
                          | [] => none
                          | transport :: rest7 =>
                              match rest7 with
                              | [] => none
                              | replay :: rest8 =>
                                  match rest8 with
                                  | [] => none
                                  | provenance :: rest9 =>
                                      match rest9 with
                                      | [] => none
                                      | nameCert :: rest10 =>
                                          match rest10 with
                                          | [] =>
                                              some
                                                (SchwarzPickDiskContractionUp.mk
                                                  (schwarzPickDiskContractionDecodeBHist disk)
                                                  (schwarzPickDiskContractionDecodeBHist map)
                                                  (schwarzPickDiskContractionDecodeBHist metric)
                                                  (schwarzPickDiskContractionDecodeBHist contraction)
                                                  (schwarzPickDiskContractionDecodeBHist boundary)
                                                  (schwarzPickDiskContractionDecodeBHist route)
                                                  (schwarzPickDiskContractionDecodeBHist transport)
                                                  (schwarzPickDiskContractionDecodeBHist replay)
                                                  (schwarzPickDiskContractionDecodeBHist provenance)
                                                  (schwarzPickDiskContractionDecodeBHist nameCert))
                                          | _extra :: _extras => none

private theorem SchwarzPickDiskContractionTasteGate_single_carrier_alignment_round_trip
    (x : SchwarzPickDiskContractionUp) :
    schwarzPickDiskContractionFromEventFlow (schwarzPickDiskContractionToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk disk map metric contraction boundary route transport replay provenance nameCert =>
      change
        some
          (SchwarzPickDiskContractionUp.mk
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist disk))
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist map))
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist metric))
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist contraction))
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist boundary))
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist route))
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist transport))
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist replay))
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist provenance))
            (schwarzPickDiskContractionDecodeBHist
              (schwarzPickDiskContractionEncodeBHist nameCert))) =
          some
            (SchwarzPickDiskContractionUp.mk disk map metric contraction boundary route
              transport replay provenance nameCert)
      rw [SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode disk,
        SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode map,
        SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode metric,
        SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode contraction,
        SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode boundary,
        SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode route,
        SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode transport,
        SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode replay,
        SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode provenance,
        SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode nameCert]

private theorem SchwarzPickDiskContractionTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SchwarzPickDiskContractionUp} :
    schwarzPickDiskContractionToEventFlow x = schwarzPickDiskContractionToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      schwarzPickDiskContractionFromEventFlow (schwarzPickDiskContractionToEventFlow x) =
        schwarzPickDiskContractionFromEventFlow (schwarzPickDiskContractionToEventFlow y) :=
    congrArg schwarzPickDiskContractionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SchwarzPickDiskContractionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SchwarzPickDiskContractionTasteGate_single_carrier_alignment_round_trip y)))

instance schwarzPickDiskContractionBHistCarrier :
    BHistCarrier SchwarzPickDiskContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := schwarzPickDiskContractionToEventFlow
  fromEventFlow := schwarzPickDiskContractionFromEventFlow

instance schwarzPickDiskContractionChapterTasteGate :
    ChapterTasteGate SchwarzPickDiskContractionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change schwarzPickDiskContractionFromEventFlow (schwarzPickDiskContractionToEventFlow x) =
      some x
    exact SchwarzPickDiskContractionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SchwarzPickDiskContractionTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def schwarzPickDiskContractionTasteGate :
    ChapterTasteGate SchwarzPickDiskContractionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  schwarzPickDiskContractionChapterTasteGate

theorem SchwarzPickDiskContractionTasteGate_single_carrier_alignment :
    (∀ h : BHist, schwarzPickDiskContractionDecodeBHist
      (schwarzPickDiskContractionEncodeBHist h) = h) ∧
      (∀ x : SchwarzPickDiskContractionUp,
        schwarzPickDiskContractionFromEventFlow
          (schwarzPickDiskContractionToEventFlow x) = some x) ∧
        (∀ x y : SchwarzPickDiskContractionUp,
          schwarzPickDiskContractionToEventFlow x =
            schwarzPickDiskContractionToEventFlow y -> x = y) ∧
          schwarzPickDiskContractionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SchwarzPickDiskContractionTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact SchwarzPickDiskContractionTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact SchwarzPickDiskContractionTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.SchwarzPickDiskContractionUp
