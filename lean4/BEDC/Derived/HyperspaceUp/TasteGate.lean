import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperspaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HyperspaceUp : Type where
  | mk
      (source subsetZero subsetOne netZero netOne directedZero directedOne tolerance
        transport continuation provenance name : BHist) : HyperspaceUp
  deriving DecidableEq

def hyperspaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperspaceEncodeBHist h

def hyperspaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperspaceDecodeBHist tail)

private theorem hyperspaceDecode_encode_bhist :
    ∀ h : BHist, hyperspaceDecodeBHist (hyperspaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hyperspaceFields : HyperspaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperspaceUp.mk source subsetZero subsetOne netZero netOne directedZero directedOne
      tolerance transport continuation provenance name =>
      [source, subsetZero, subsetOne, netZero, netOne, directedZero, directedOne,
        tolerance, transport, continuation, provenance, name]

def hyperspaceToEventFlow : HyperspaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperspaceFields x).map hyperspaceEncodeBHist

def hyperspaceFromEventFlow : EventFlow → Option HyperspaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | subsetZero :: rest1 =>
          match rest1 with
          | [] => none
          | subsetOne :: rest2 =>
              match rest2 with
              | [] => none
              | netZero :: rest3 =>
                  match rest3 with
                  | [] => none
                  | netOne :: rest4 =>
                      match rest4 with
                      | [] => none
                      | directedZero :: rest5 =>
                          match rest5 with
                          | [] => none
                          | directedOne :: rest6 =>
                              match rest6 with
                              | [] => none
                              | tolerance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | transport :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | continuation :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | provenance :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | name :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (HyperspaceUp.mk
                                                          (hyperspaceDecodeBHist source)
                                                          (hyperspaceDecodeBHist subsetZero)
                                                          (hyperspaceDecodeBHist subsetOne)
                                                          (hyperspaceDecodeBHist netZero)
                                                          (hyperspaceDecodeBHist netOne)
                                                          (hyperspaceDecodeBHist directedZero)
                                                          (hyperspaceDecodeBHist directedOne)
                                                          (hyperspaceDecodeBHist tolerance)
                                                          (hyperspaceDecodeBHist transport)
                                                          (hyperspaceDecodeBHist continuation)
                                                          (hyperspaceDecodeBHist provenance)
                                                          (hyperspaceDecodeBHist name))
                                                  | _ :: _ => none

private theorem hyperspace_round_trip :
    ∀ x : HyperspaceUp, hyperspaceFromEventFlow (hyperspaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source subsetZero subsetOne netZero netOne directedZero directedOne tolerance
      transport continuation provenance name =>
      change
        some
          (HyperspaceUp.mk
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist source))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist subsetZero))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist subsetOne))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist netZero))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist netOne))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist directedZero))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist directedOne))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist tolerance))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist transport))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist continuation))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist provenance))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist name))) =
          some
            (HyperspaceUp.mk source subsetZero subsetOne netZero netOne directedZero
              directedOne tolerance transport continuation provenance name)
      rw [hyperspaceDecode_encode_bhist source,
        hyperspaceDecode_encode_bhist subsetZero,
        hyperspaceDecode_encode_bhist subsetOne,
        hyperspaceDecode_encode_bhist netZero,
        hyperspaceDecode_encode_bhist netOne,
        hyperspaceDecode_encode_bhist directedZero,
        hyperspaceDecode_encode_bhist directedOne,
        hyperspaceDecode_encode_bhist tolerance,
        hyperspaceDecode_encode_bhist transport,
        hyperspaceDecode_encode_bhist continuation,
        hyperspaceDecode_encode_bhist provenance,
        hyperspaceDecode_encode_bhist name]

private theorem hyperspaceToEventFlow_injective {x y : HyperspaceUp} :
    hyperspaceToEventFlow x = hyperspaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperspaceFromEventFlow (hyperspaceToEventFlow x) =
        hyperspaceFromEventFlow (hyperspaceToEventFlow y) :=
    congrArg hyperspaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperspace_round_trip x).symm (Eq.trans hread (hyperspace_round_trip y)))

private theorem hyperspace_fields_faithful :
    ∀ x y : HyperspaceUp, hyperspaceFields x = hyperspaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source subsetZero subsetOne netZero netOne directedZero directedOne tolerance
      transport continuation provenance name =>
      cases y with
      | mk source' subsetZero' subsetOne' netZero' netOne' directedZero' directedOne'
          tolerance' transport' continuation' provenance' name' =>
          cases hfields
          rfl

instance hyperspaceBHistCarrier : BHistCarrier HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperspaceToEventFlow
  fromEventFlow := hyperspaceFromEventFlow

instance hyperspaceChapterTasteGate : ChapterTasteGate HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyperspaceFromEventFlow (hyperspaceToEventFlow x) = some x
    exact hyperspace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperspaceToEventFlow_injective heq)

instance hyperspaceFieldFaithful : FieldFaithful HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperspaceFields
  field_faithful := hyperspace_fields_faithful

instance hyperspaceNontrivial : Nontrivial HyperspaceUp where
  witness_pair :=
    ⟨HyperspaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperspaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HyperspaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hyperspaceChapterTasteGate

theorem HyperspaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HyperspaceUp) ∧
      Nonempty (FieldFaithful HyperspaceUp) ∧
      Nonempty (Nontrivial HyperspaceUp) ∧
      (∀ h : BHist, hyperspaceDecodeBHist (hyperspaceEncodeBHist h) = h) ∧
      (∀ x : HyperspaceUp, hyperspaceFromEventFlow (hyperspaceToEventFlow x) = some x) ∧
      (∀ x y : HyperspaceUp,
        hyperspaceToEventFlow x = hyperspaceToEventFlow y → x = y) ∧
      hyperspaceEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨⟨hyperspaceChapterTasteGate⟩, ⟨hyperspaceFieldFaithful⟩,
    ⟨hyperspaceNontrivial⟩, hyperspaceDecode_encode_bhist, hyperspace_round_trip,
    fun _ _ heq => hyperspaceToEventFlow_injective heq, rfl⟩

end BEDC.Derived.HyperspaceUp.TasteGate
