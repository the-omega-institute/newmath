import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MultiHistSuperpositionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MultiHistSuperpositionUp : Type where
  | mk :
      (config refinement zeroRows causal rate phase history psameRoutes contRoutes provenance
        nameCert : BHist) →
      MultiHistSuperpositionUp
  deriving DecidableEq

def multiHistSuperpositionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: multiHistSuperpositionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: multiHistSuperpositionEncodeBHist h

def multiHistSuperpositionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (multiHistSuperpositionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (multiHistSuperpositionDecodeBHist tail)

private theorem multiHistSuperpositionDecode_encode_bhist :
    ∀ h : BHist,
      multiHistSuperpositionDecodeBHist (multiHistSuperpositionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem multiHistSuperposition_mk_congr
    {config config' refinement refinement' zeroRows zeroRows' causal causal' rate rate'
      phase phase' history history' psameRoutes psameRoutes' contRoutes contRoutes'
      provenance provenance' nameCert nameCert' : BHist}
    (hConfig : config' = config)
    (hRefinement : refinement' = refinement)
    (hZeroRows : zeroRows' = zeroRows)
    (hCausal : causal' = causal)
    (hRate : rate' = rate)
    (hPhase : phase' = phase)
    (hHistory : history' = history)
    (hPsameRoutes : psameRoutes' = psameRoutes)
    (hContRoutes : contRoutes' = contRoutes)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    MultiHistSuperpositionUp.mk config' refinement' zeroRows' causal' rate' phase' history'
        psameRoutes' contRoutes' provenance' nameCert' =
      MultiHistSuperpositionUp.mk config refinement zeroRows causal rate phase history
        psameRoutes contRoutes provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hConfig
  cases hRefinement
  cases hZeroRows
  cases hCausal
  cases hRate
  cases hPhase
  cases hHistory
  cases hPsameRoutes
  cases hContRoutes
  cases hProvenance
  cases hNameCert
  rfl

def multiHistSuperpositionToEventFlow : MultiHistSuperpositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MultiHistSuperpositionUp.mk config refinement zeroRows causal rate phase history
      psameRoutes contRoutes provenance nameCert =>
      [[BMark.b0],
        multiHistSuperpositionEncodeBHist config,
        [BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist refinement,
        [BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist zeroRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist causal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist rate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist phase,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist history,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        multiHistSuperpositionEncodeBHist psameRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist contRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist nameCert]

def multiHistSuperpositionFromEventFlow : EventFlow → Option MultiHistSuperpositionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | config :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | refinement :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | zeroRows :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | causal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | rate :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | phase :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | history :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | psameRoutes :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | contRoutes :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | nameCert :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (MultiHistSuperpositionUp.mk
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    config)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    refinement)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    zeroRows)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    causal)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    rate)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    phase)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    history)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    psameRoutes)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    contRoutes)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    provenance)
                                                                                                  (multiHistSuperpositionDecodeBHist
                                                                                                    nameCert))
                                                                                          | _ :: _ => none

private theorem multiHistSuperposition_round_trip :
    ∀ x : MultiHistSuperpositionUp,
      multiHistSuperpositionFromEventFlow (multiHistSuperpositionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk config refinement zeroRows causal rate phase history psameRoutes contRoutes provenance
      nameCert =>
      change
        some
          (MultiHistSuperpositionUp.mk
            (multiHistSuperpositionDecodeBHist (multiHistSuperpositionEncodeBHist config))
            (multiHistSuperpositionDecodeBHist
              (multiHistSuperpositionEncodeBHist refinement))
            (multiHistSuperpositionDecodeBHist (multiHistSuperpositionEncodeBHist zeroRows))
            (multiHistSuperpositionDecodeBHist (multiHistSuperpositionEncodeBHist causal))
            (multiHistSuperpositionDecodeBHist (multiHistSuperpositionEncodeBHist rate))
            (multiHistSuperpositionDecodeBHist (multiHistSuperpositionEncodeBHist phase))
            (multiHistSuperpositionDecodeBHist (multiHistSuperpositionEncodeBHist history))
            (multiHistSuperpositionDecodeBHist
              (multiHistSuperpositionEncodeBHist psameRoutes))
            (multiHistSuperpositionDecodeBHist
              (multiHistSuperpositionEncodeBHist contRoutes))
            (multiHistSuperpositionDecodeBHist
              (multiHistSuperpositionEncodeBHist provenance))
            (multiHistSuperpositionDecodeBHist
              (multiHistSuperpositionEncodeBHist nameCert))) =
          some
            (MultiHistSuperpositionUp.mk config refinement zeroRows causal rate phase history
              psameRoutes contRoutes provenance nameCert)
      exact
        congrArg some
          (multiHistSuperposition_mk_congr
            (multiHistSuperpositionDecode_encode_bhist config)
            (multiHistSuperpositionDecode_encode_bhist refinement)
            (multiHistSuperpositionDecode_encode_bhist zeroRows)
            (multiHistSuperpositionDecode_encode_bhist causal)
            (multiHistSuperpositionDecode_encode_bhist rate)
            (multiHistSuperpositionDecode_encode_bhist phase)
            (multiHistSuperpositionDecode_encode_bhist history)
            (multiHistSuperpositionDecode_encode_bhist psameRoutes)
            (multiHistSuperpositionDecode_encode_bhist contRoutes)
            (multiHistSuperpositionDecode_encode_bhist provenance)
            (multiHistSuperpositionDecode_encode_bhist nameCert))

private theorem multiHistSuperPositionToEventFlow_injective {x y : MultiHistSuperpositionUp} :
    multiHistSuperpositionToEventFlow x = multiHistSuperpositionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      multiHistSuperpositionFromEventFlow (multiHistSuperpositionToEventFlow x) =
        multiHistSuperpositionFromEventFlow (multiHistSuperpositionToEventFlow y) :=
    congrArg multiHistSuperpositionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (multiHistSuperposition_round_trip x).symm
      (Eq.trans hread (multiHistSuperposition_round_trip y)))

def multiHistSuperPositionToEventFlow : MultiHistSuperpositionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MultiHistSuperpositionUp.mk config refinement zeroRows causal rate phase history
      psameRoutes contRoutes provenance nameCert =>
      [[BMark.b0],
        multiHistSuperpositionEncodeBHist config,
        [BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist refinement,
        [BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist zeroRows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist causal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist rate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist phase,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist history,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        multiHistSuperpositionEncodeBHist psameRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist contRoutes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        multiHistSuperpositionEncodeBHist nameCert]

private theorem multiHistSuperPositionToEventFlow_matches
    (x : MultiHistSuperpositionUp) :
    multiHistSuperPositionToEventFlow x = multiHistSuperpositionToEventFlow x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x
  rfl

instance multiHistSuperpositionBHistCarrier : BHistCarrier MultiHistSuperpositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := multiHistSuperpositionToEventFlow
  fromEventFlow := multiHistSuperpositionFromEventFlow

instance multiHistSuperpositionChapterTasteGate : ChapterTasteGate MultiHistSuperpositionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change multiHistSuperpositionFromEventFlow (multiHistSuperpositionToEventFlow x) = some x
    exact multiHistSuperposition_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (multiHistSuperPositionToEventFlow_injective heq)

theorem MultiHistSuperpositionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      multiHistSuperpositionDecodeBHist (multiHistSuperpositionEncodeBHist h) = h) ∧
      (∀ x : MultiHistSuperpositionUp,
        multiHistSuperpositionFromEventFlow (multiHistSuperpositionToEventFlow x) = some x) ∧
        (∀ x y : MultiHistSuperpositionUp,
          multiHistSuperPositionToEventFlow x = multiHistSuperpositionToEventFlow y → x = y) ∧
          (∀ (x : MultiHistSuperpositionUp) w m,
            List.Mem w (multiHistSuperpositionToEventFlow x) → List.Mem m w →
              m = BMark.b0 ∨ m = BMark.b1) ∧
            multiHistSuperpositionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact multiHistSuperpositionDecode_encode_bhist
  · constructor
    · exact multiHistSuperposition_round_trip
    · constructor
      · intro x y heq
        exact
          multiHistSuperPositionToEventFlow_injective
            (Eq.trans (multiHistSuperPositionToEventFlow_matches x).symm heq)
      · constructor
        · intro x w m hw hm
          cases m with
          | b0 =>
              exact Or.inl rfl
          | b1 =>
              exact Or.inr rfl
        · rfl

end BEDC.Derived.MultiHistSuperpositionUp
