import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactModulusCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactModulusCoverUp : Type where
  | mk :
      (compactSource continuous tolerance bundle covering pointwise handoff radiusFamily
        transports routes provenance : BHist) →
      CompactModulusCoverUp
  deriving DecidableEq

def compactModulusCoverEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactModulusCoverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactModulusCoverEncodeBHist h

def compactModulusCoverDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactModulusCoverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactModulusCoverDecodeBHist tail)

private theorem compactModulusCoverDecode_encode_bhist :
    ∀ h : BHist, compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactModulusCoverToEventFlow : CompactModulusCoverUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompactModulusCoverUp.mk compactSource continuous tolerance bundle covering pointwise
      handoff radiusFamily transports routes provenance =>
      [[BMark.b0],
        compactModulusCoverEncodeBHist compactSource,
        [BMark.b1, BMark.b0],
        compactModulusCoverEncodeBHist continuous,
        [BMark.b1, BMark.b1, BMark.b0],
        compactModulusCoverEncodeBHist tolerance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusCoverEncodeBHist bundle,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusCoverEncodeBHist covering,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusCoverEncodeBHist pointwise,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusCoverEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compactModulusCoverEncodeBHist radiusFamily,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compactModulusCoverEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        compactModulusCoverEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compactModulusCoverEncodeBHist provenance]

def compactModulusCoverFromEventFlow : EventFlow → Option CompactModulusCoverUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | compactSource :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | continuous :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | tolerance :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | bundle :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | covering :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | pointwise :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | handoff :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | radiusFamily :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transports :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | routes :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (CompactModulusCoverUp.mk
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    compactSource)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    continuous)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    tolerance)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    bundle)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    covering)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    pointwise)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    handoff)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    radiusFamily)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    transports)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    routes)
                                                                                                  (compactModulusCoverDecodeBHist
                                                                                                    provenance))
                                                                                          | _ :: _ => none

private theorem compactModulusCover_round_trip :
    ∀ x : CompactModulusCoverUp,
      compactModulusCoverFromEventFlow (compactModulusCoverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactSource continuous tolerance bundle covering pointwise handoff radiusFamily
      transports routes provenance =>
      change
        some
          (CompactModulusCoverUp.mk
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist compactSource))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist continuous))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist tolerance))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist bundle))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist covering))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist pointwise))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist handoff))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist radiusFamily))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist transports))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist routes))
            (compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist provenance))) =
          some
            (CompactModulusCoverUp.mk compactSource continuous tolerance bundle covering pointwise
              handoff radiusFamily transports routes provenance)
      rw [compactModulusCoverDecode_encode_bhist compactSource,
        compactModulusCoverDecode_encode_bhist continuous,
        compactModulusCoverDecode_encode_bhist tolerance,
        compactModulusCoverDecode_encode_bhist bundle,
        compactModulusCoverDecode_encode_bhist covering,
        compactModulusCoverDecode_encode_bhist pointwise,
        compactModulusCoverDecode_encode_bhist handoff,
        compactModulusCoverDecode_encode_bhist radiusFamily,
        compactModulusCoverDecode_encode_bhist transports,
        compactModulusCoverDecode_encode_bhist routes,
        compactModulusCoverDecode_encode_bhist provenance]

private theorem compactModulusCoverToEventFlow_injective {x y : CompactModulusCoverUp} :
    compactModulusCoverToEventFlow x = compactModulusCoverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactModulusCoverFromEventFlow (compactModulusCoverToEventFlow x) =
        compactModulusCoverFromEventFlow (compactModulusCoverToEventFlow y) :=
    congrArg compactModulusCoverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactModulusCover_round_trip x).symm
      (Eq.trans hread (compactModulusCover_round_trip y)))

instance compactModulusCoverBHistCarrier : BHistCarrier CompactModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactModulusCoverToEventFlow
  fromEventFlow := compactModulusCoverFromEventFlow

instance compactModulusCoverChapterTasteGate : ChapterTasteGate CompactModulusCoverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compactModulusCoverFromEventFlow (compactModulusCoverToEventFlow x) = some x
    exact compactModulusCover_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactModulusCoverToEventFlow_injective heq)

theorem CompactModulusCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist, compactModulusCoverDecodeBHist (compactModulusCoverEncodeBHist h) = h) ∧
      (∀ x : CompactModulusCoverUp,
        compactModulusCoverFromEventFlow (compactModulusCoverToEventFlow x) = some x) ∧
        (∀ x y : CompactModulusCoverUp,
          compactModulusCoverToEventFlow x = compactModulusCoverToEventFlow y → x = y) ∧
          compactModulusCoverEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact compactModulusCoverDecode_encode_bhist
  · constructor
    · exact compactModulusCover_round_trip
    · constructor
      · intro x y heq
        exact compactModulusCoverToEventFlow_injective heq
      · rfl

end BEDC.Derived.CompactModulusCoverUp
