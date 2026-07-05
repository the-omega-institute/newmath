import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeineCantorModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeineCantorModulusUp : Type where
  | mk
      (source target map precision net centers radii modulus triangle transport replay
        provenance name : BHist) :
      HeineCantorModulusUp
  deriving DecidableEq

def heineCantorModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heineCantorModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heineCantorModulusEncodeBHist h

def heineCantorModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heineCantorModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heineCantorModulusDecodeBHist tail)

private theorem heineCantorModulusDecode_encode_bhist :
    ∀ h : BHist, heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def heineCantorModulusToEventFlow : HeineCantorModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HeineCantorModulusUp.mk source target map precision net centers radii modulus triangle
      transport replay provenance name =>
      [[BMark.b0],
        heineCantorModulusEncodeBHist source,
        [BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist map,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist precision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist net,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist centers,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist radii,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        heineCantorModulusEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist triangle,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorModulusEncodeBHist name]

def heineCantorModulusFromEventFlow : EventFlow → Option HeineCantorModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | target :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | map :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | precision :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | net :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | centers :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | radii :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | modulus :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | triangle :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | transport :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | replay :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | provenance :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] => none
                                                                                                  | _tag12 :: rest24 =>
                                                                                                      match rest24 with
                                                                                                      | [] => none
                                                                                                      | name :: rest25 =>
                                                                                                          match rest25 with
                                                                                                          | [] =>
                                                                                                              some
                                                                                                                (HeineCantorModulusUp.mk
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    source)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    target)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    map)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    precision)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    net)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    centers)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    radii)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    modulus)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    triangle)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    transport)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    replay)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    provenance)
                                                                                                                  (heineCantorModulusDecodeBHist
                                                                                                                    name))
                                                                                                          | _ :: _ => none

private theorem heineCantorModulus_round_trip :
    ∀ x : HeineCantorModulusUp,
      heineCantorModulusFromEventFlow (heineCantorModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target map precision net centers radii modulus triangle transport replay
      provenance name =>
      change
        some
          (HeineCantorModulusUp.mk
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist source))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist target))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist map))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist precision))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist net))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist centers))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist radii))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist modulus))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist triangle))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist transport))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist replay))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist provenance))
            (heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist name))) =
          some
            (HeineCantorModulusUp.mk source target map precision net centers radii modulus
              triangle transport replay provenance name)
      rw [heineCantorModulusDecode_encode_bhist source,
        heineCantorModulusDecode_encode_bhist target,
        heineCantorModulusDecode_encode_bhist map,
        heineCantorModulusDecode_encode_bhist precision,
        heineCantorModulusDecode_encode_bhist net,
        heineCantorModulusDecode_encode_bhist centers,
        heineCantorModulusDecode_encode_bhist radii,
        heineCantorModulusDecode_encode_bhist modulus,
        heineCantorModulusDecode_encode_bhist triangle,
        heineCantorModulusDecode_encode_bhist transport,
        heineCantorModulusDecode_encode_bhist replay,
        heineCantorModulusDecode_encode_bhist provenance,
        heineCantorModulusDecode_encode_bhist name]

private theorem heineCantorModulusToEventFlow_injective {x y : HeineCantorModulusUp} :
    heineCantorModulusToEventFlow x = heineCantorModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heineCantorModulusFromEventFlow (heineCantorModulusToEventFlow x) =
        heineCantorModulusFromEventFlow (heineCantorModulusToEventFlow y) :=
    congrArg heineCantorModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (heineCantorModulus_round_trip x).symm
      (Eq.trans hread (heineCantorModulus_round_trip y)))

instance heineCantorModulusBHistCarrier : BHistCarrier HeineCantorModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heineCantorModulusToEventFlow
  fromEventFlow := heineCantorModulusFromEventFlow

instance heineCantorModulusChapterTasteGate : ChapterTasteGate HeineCantorModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change heineCantorModulusFromEventFlow (heineCantorModulusToEventFlow x) = some x
    exact heineCantorModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (heineCantorModulusToEventFlow_injective heq)

theorem HeineCantorModulusTasteGate_single_carrier_alignment :
    (forall h : BHist, heineCantorModulusDecodeBHist (heineCantorModulusEncodeBHist h) = h) ∧
      (forall x : HeineCantorModulusUp,
        heineCantorModulusFromEventFlow (heineCantorModulusToEventFlow x) = some x) ∧
      (forall x y : HeineCantorModulusUp,
        heineCantorModulusToEventFlow x = heineCantorModulusToEventFlow y -> x = y) ∧
      heineCantorModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact heineCantorModulusDecode_encode_bhist
  · constructor
    · exact heineCantorModulus_round_trip
    · constructor
      · intro x y heq
        exact heineCantorModulusToEventFlow_injective heq
      · rfl

end BEDC.Derived.HeineCantorModulusUp
