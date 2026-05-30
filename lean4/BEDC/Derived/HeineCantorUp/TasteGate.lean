import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HeineCantorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HeineCantorUp : Type where
  | mk
      (source target map precision finiteNet radii locatedMesh modulus estimate transport replay
        provenance name : BHist) :
      HeineCantorUp
  deriving DecidableEq

def heineCantorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: heineCantorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: heineCantorEncodeBHist h

def heineCantorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (heineCantorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (heineCantorDecodeBHist tail)

private theorem heineCantorDecode_encode_bhist :
    ∀ h : BHist, heineCantorDecodeBHist (heineCantorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def heineCantorToEventFlow : HeineCantorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HeineCantorUp.mk source target map precision finiteNet radii locatedMesh modulus estimate
      transport replay provenance name =>
      [[BMark.b0],
        heineCantorEncodeBHist source,
        [BMark.b1, BMark.b0],
        heineCantorEncodeBHist target,
        [BMark.b1, BMark.b1, BMark.b0],
        heineCantorEncodeBHist map,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorEncodeBHist precision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorEncodeBHist finiteNet,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorEncodeBHist radii,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorEncodeBHist locatedMesh,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        heineCantorEncodeBHist modulus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        heineCantorEncodeBHist estimate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        heineCantorEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        heineCantorEncodeBHist name]

def heineCantorFromEventFlow : EventFlow → Option HeineCantorUp
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
                                      | finiteNet :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | radii :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | locatedMesh :: rest13 =>
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
                                                                      | estimate :: rest17 =>
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
                                                                                                                (HeineCantorUp.mk
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    source)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    target)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    map)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    precision)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    finiteNet)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    radii)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    locatedMesh)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    modulus)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    estimate)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    transport)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    replay)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    provenance)
                                                                                                                  (heineCantorDecodeBHist
                                                                                                                    name))
                                                                                                          | _ :: _ => none

private theorem heineCantor_round_trip :
    ∀ x : HeineCantorUp, heineCantorFromEventFlow (heineCantorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source target map precision finiteNet radii locatedMesh modulus estimate transport replay
      provenance name =>
      change
        some
          (HeineCantorUp.mk
            (heineCantorDecodeBHist (heineCantorEncodeBHist source))
            (heineCantorDecodeBHist (heineCantorEncodeBHist target))
            (heineCantorDecodeBHist (heineCantorEncodeBHist map))
            (heineCantorDecodeBHist (heineCantorEncodeBHist precision))
            (heineCantorDecodeBHist (heineCantorEncodeBHist finiteNet))
            (heineCantorDecodeBHist (heineCantorEncodeBHist radii))
            (heineCantorDecodeBHist (heineCantorEncodeBHist locatedMesh))
            (heineCantorDecodeBHist (heineCantorEncodeBHist modulus))
            (heineCantorDecodeBHist (heineCantorEncodeBHist estimate))
            (heineCantorDecodeBHist (heineCantorEncodeBHist transport))
            (heineCantorDecodeBHist (heineCantorEncodeBHist replay))
            (heineCantorDecodeBHist (heineCantorEncodeBHist provenance))
            (heineCantorDecodeBHist (heineCantorEncodeBHist name))) =
          some
            (HeineCantorUp.mk source target map precision finiteNet radii locatedMesh modulus
              estimate transport replay provenance name)
      rw [heineCantorDecode_encode_bhist source, heineCantorDecode_encode_bhist target,
        heineCantorDecode_encode_bhist map, heineCantorDecode_encode_bhist precision,
        heineCantorDecode_encode_bhist finiteNet, heineCantorDecode_encode_bhist radii,
        heineCantorDecode_encode_bhist locatedMesh, heineCantorDecode_encode_bhist modulus,
        heineCantorDecode_encode_bhist estimate, heineCantorDecode_encode_bhist transport,
        heineCantorDecode_encode_bhist replay, heineCantorDecode_encode_bhist provenance,
        heineCantorDecode_encode_bhist name]

private theorem heineCantorToEventFlow_injective {x y : HeineCantorUp} :
    heineCantorToEventFlow x = heineCantorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      heineCantorFromEventFlow (heineCantorToEventFlow x) =
        heineCantorFromEventFlow (heineCantorToEventFlow y) :=
    congrArg heineCantorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (heineCantor_round_trip x).symm
      (Eq.trans hread (heineCantor_round_trip y)))

instance heineCantorBHistCarrier : BHistCarrier HeineCantorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := heineCantorToEventFlow
  fromEventFlow := heineCantorFromEventFlow

instance heineCantorChapterTasteGate : ChapterTasteGate HeineCantorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change heineCantorFromEventFlow (heineCantorToEventFlow x) = some x
    exact heineCantor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (heineCantorToEventFlow_injective heq)

theorem HeineCantorTasteGate_single_carrier_alignment :
    (∀ h : BHist, heineCantorDecodeBHist (heineCantorEncodeBHist h) = h) ∧
      (∀ x : HeineCantorUp, heineCantorFromEventFlow (heineCantorToEventFlow x) = some x) ∧
      (∀ x y : HeineCantorUp, heineCantorToEventFlow x = heineCantorToEventFlow y → x = y) ∧
      heineCantorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact heineCantorDecode_encode_bhist
  · constructor
    · exact heineCantor_round_trip
    · constructor
      · intro x y heq
        exact heineCantorToEventFlow_injective heq
      · rfl

end BEDC.Derived.HeineCantorUp
