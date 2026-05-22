import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCauchySeriesUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCauchySeriesUp : Type where
  | mk :
      (term partialSum window readback dyadic threshold endpoint transport replay provenance
        localName : BHist) ->
        UniformCauchySeriesUp
  deriving DecidableEq

def uniformCauchySeriesEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCauchySeriesEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCauchySeriesEncodeBHist h

def uniformCauchySeriesDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCauchySeriesDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCauchySeriesDecodeBHist tail)

theorem UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def uniformCauchySeriesFields : UniformCauchySeriesUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCauchySeriesUp.mk term partialSum window readback dyadic threshold endpoint
      transport replay provenance localName =>
      [term, partialSum, window, readback, dyadic, threshold, endpoint, transport, replay,
        provenance, localName]

def uniformCauchySeriesToEventFlow : UniformCauchySeriesUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformCauchySeriesFields x).map uniformCauchySeriesEncodeBHist

def uniformCauchySeriesFromEventFlow : EventFlow -> Option UniformCauchySeriesUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | term :: rest0 =>
      match rest0 with
      | [] => none
      | partialSum :: rest1 =>
          match rest1 with
          | [] => none
          | window :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadic :: rest4 =>
                      match rest4 with
                      | [] => none
                      | threshold :: rest5 =>
                          match rest5 with
                          | [] => none
                          | endpoint :: rest6 =>
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
                                          | localName :: rest10 =>
                                              match rest10 with
                                              | [] =>
                                                  some
                                                    (UniformCauchySeriesUp.mk
                                                      (uniformCauchySeriesDecodeBHist term)
                                                      (uniformCauchySeriesDecodeBHist partialSum)
                                                      (uniformCauchySeriesDecodeBHist window)
                                                      (uniformCauchySeriesDecodeBHist readback)
                                                      (uniformCauchySeriesDecodeBHist dyadic)
                                                      (uniformCauchySeriesDecodeBHist threshold)
                                                      (uniformCauchySeriesDecodeBHist endpoint)
                                                      (uniformCauchySeriesDecodeBHist transport)
                                                      (uniformCauchySeriesDecodeBHist replay)
                                                      (uniformCauchySeriesDecodeBHist provenance)
                                                      (uniformCauchySeriesDecodeBHist localName))
                                              | _ :: _ => none

theorem UniformCauchySeriesTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCauchySeriesUp,
      uniformCauchySeriesFromEventFlow (uniformCauchySeriesToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term partialSum window readback dyadic threshold endpoint transport replay provenance
      localName =>
      change
        some
          (UniformCauchySeriesUp.mk
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist term))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist partialSum))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist window))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist readback))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist dyadic))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist threshold))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist endpoint))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist transport))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist replay))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist provenance))
            (uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist localName))) =
          some
            (UniformCauchySeriesUp.mk term partialSum window readback dyadic threshold
              endpoint transport replay provenance localName)
      rw [UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode term,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode partialSum,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode window,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode readback,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode dyadic,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode threshold,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode endpoint,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode transport,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode replay,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode provenance,
        UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode localName]

theorem UniformCauchySeriesTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UniformCauchySeriesUp} :
    uniformCauchySeriesToEventFlow x = uniformCauchySeriesToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCauchySeriesFromEventFlow (uniformCauchySeriesToEventFlow x) =
        uniformCauchySeriesFromEventFlow (uniformCauchySeriesToEventFlow y) :=
    congrArg uniformCauchySeriesFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformCauchySeriesTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformCauchySeriesTasteGate_single_carrier_alignment_round_trip y)))

instance uniformCauchySeriesBHistCarrier : BHistCarrier UniformCauchySeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCauchySeriesToEventFlow
  fromEventFlow := uniformCauchySeriesFromEventFlow

instance uniformCauchySeriesChapterTasteGate : ChapterTasteGate UniformCauchySeriesUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (UniformCauchySeriesTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformCauchySeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem UniformCauchySeriesTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformCauchySeriesDecodeBHist (uniformCauchySeriesEncodeBHist h) = h) ∧
      (∀ x : UniformCauchySeriesUp,
        uniformCauchySeriesFromEventFlow (uniformCauchySeriesToEventFlow x) = some x) ∧
        (∀ x y : UniformCauchySeriesUp,
          uniformCauchySeriesToEventFlow x = uniformCauchySeriesToEventFlow y -> x = y) ∧
          uniformCauchySeriesEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact UniformCauchySeriesTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · exact UniformCauchySeriesTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact UniformCauchySeriesTasteGate_single_carrier_alignment_toEventFlow_injective heq
      · rfl

end BEDC.Derived.UniformCauchySeriesUp.TasteGate
