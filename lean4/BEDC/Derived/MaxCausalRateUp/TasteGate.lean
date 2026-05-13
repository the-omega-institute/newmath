import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MaxCausalRateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MaxCausalRateUp : Type where
  | mk (configuration witnesses bound comparisons hsameTransport psameStability routes provenance
      nameCert : BHist) : MaxCausalRateUp
  deriving DecidableEq

def maxCausalRateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: maxCausalRateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: maxCausalRateEncodeBHist h

def maxCausalRateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (maxCausalRateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (maxCausalRateDecodeBHist tail)

private theorem maxCausalRateDecode_encode_bhist :
    ∀ h : BHist, maxCausalRateDecodeBHist (maxCausalRateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def maxCausalRateToEventFlow : MaxCausalRateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MaxCausalRateUp.mk configuration witnesses bound comparisons hsameTransport psameStability
      routes provenance nameCert =>
      [[BMark.b0],
        maxCausalRateEncodeBHist configuration,
        [BMark.b1, BMark.b0],
        maxCausalRateEncodeBHist witnesses,
        [BMark.b1, BMark.b1, BMark.b0],
        maxCausalRateEncodeBHist bound,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        maxCausalRateEncodeBHist comparisons,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        maxCausalRateEncodeBHist hsameTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        maxCausalRateEncodeBHist psameStability,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        maxCausalRateEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        maxCausalRateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        maxCausalRateEncodeBHist nameCert]

def maxCausalRateFromEventFlow : EventFlow → Option MaxCausalRateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | configuration :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | witnesses :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | bound :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | comparisons :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | hsameTransport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | psameStability :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MaxCausalRateUp.mk
                                                                                  (maxCausalRateDecodeBHist
                                                                                    configuration)
                                                                                  (maxCausalRateDecodeBHist
                                                                                    witnesses)
                                                                                  (maxCausalRateDecodeBHist
                                                                                    bound)
                                                                                  (maxCausalRateDecodeBHist
                                                                                    comparisons)
                                                                                  (maxCausalRateDecodeBHist
                                                                                    hsameTransport)
                                                                                  (maxCausalRateDecodeBHist
                                                                                    psameStability)
                                                                                  (maxCausalRateDecodeBHist
                                                                                    routes)
                                                                                  (maxCausalRateDecodeBHist
                                                                                    provenance)
                                                                                  (maxCausalRateDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem maxCausalRate_round_trip :
    ∀ x : MaxCausalRateUp,
      maxCausalRateFromEventFlow (maxCausalRateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk configuration witnesses bound comparisons hsameTransport psameStability routes
      provenance nameCert =>
      change
        some (MaxCausalRateUp.mk
          (maxCausalRateDecodeBHist (maxCausalRateEncodeBHist configuration))
          (maxCausalRateDecodeBHist (maxCausalRateEncodeBHist witnesses))
          (maxCausalRateDecodeBHist (maxCausalRateEncodeBHist bound))
          (maxCausalRateDecodeBHist (maxCausalRateEncodeBHist comparisons))
          (maxCausalRateDecodeBHist (maxCausalRateEncodeBHist hsameTransport))
          (maxCausalRateDecodeBHist (maxCausalRateEncodeBHist psameStability))
          (maxCausalRateDecodeBHist (maxCausalRateEncodeBHist routes))
          (maxCausalRateDecodeBHist (maxCausalRateEncodeBHist provenance))
          (maxCausalRateDecodeBHist (maxCausalRateEncodeBHist nameCert))) =
          some (MaxCausalRateUp.mk configuration witnesses bound comparisons hsameTransport
            psameStability routes provenance nameCert)
      rw [maxCausalRateDecode_encode_bhist configuration,
        maxCausalRateDecode_encode_bhist witnesses,
        maxCausalRateDecode_encode_bhist bound,
        maxCausalRateDecode_encode_bhist comparisons,
        maxCausalRateDecode_encode_bhist hsameTransport,
        maxCausalRateDecode_encode_bhist psameStability,
        maxCausalRateDecode_encode_bhist routes,
        maxCausalRateDecode_encode_bhist provenance,
        maxCausalRateDecode_encode_bhist nameCert]

private theorem maxCausalRateToEventFlow_injective {x y : MaxCausalRateUp} :
    maxCausalRateToEventFlow x = maxCausalRateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      maxCausalRateFromEventFlow (maxCausalRateToEventFlow x) =
        maxCausalRateFromEventFlow (maxCausalRateToEventFlow y) :=
    congrArg maxCausalRateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (maxCausalRate_round_trip x).symm
      (Eq.trans hread (maxCausalRate_round_trip y)))

instance maxCausalRateBHistCarrier : BHistCarrier MaxCausalRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := maxCausalRateToEventFlow
  fromEventFlow := maxCausalRateFromEventFlow

instance maxCausalRateChapterTasteGate : ChapterTasteGate MaxCausalRateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change maxCausalRateFromEventFlow (maxCausalRateToEventFlow x) = some x
    exact maxCausalRate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (maxCausalRateToEventFlow_injective heq)

def taste_gate : ChapterTasteGate MaxCausalRateUp :=
  maxCausalRateChapterTasteGate

theorem MaxCausalRateTasteGate_single_carrier_alignment :
    (∀ h : BHist, maxCausalRateDecodeBHist (maxCausalRateEncodeBHist h) = h) ∧
      (∀ x : MaxCausalRateUp,
        maxCausalRateFromEventFlow (maxCausalRateToEventFlow x) = some x) ∧
        (∀ x y : MaxCausalRateUp,
          maxCausalRateToEventFlow x = maxCausalRateToEventFlow y → x = y) ∧
          maxCausalRateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact maxCausalRateDecode_encode_bhist
  · constructor
    · exact maxCausalRate_round_trip
    · constructor
      · intro x y heq
        exact maxCausalRateToEventFlow_injective heq
      · rfl

end BEDC.Derived.MaxCausalRateUp
