import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NatRealEmbeddingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NatRealEmbeddingUp : Type where
  | mk
      (source rationalConstant constantWindows regularReadback dyadicTolerance realSeal transport
        replay provenance name : BHist) :
      NatRealEmbeddingUp
  deriving DecidableEq

def natRealEmbeddingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: natRealEmbeddingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: natRealEmbeddingEncodeBHist h

def natRealEmbeddingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (natRealEmbeddingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (natRealEmbeddingDecodeBHist tail)

private theorem NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def natRealEmbeddingFields : NatRealEmbeddingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NatRealEmbeddingUp.mk source rationalConstant constantWindows regularReadback
      dyadicTolerance realSeal transport replay provenance name =>
      [source, rationalConstant, constantWindows, regularReadback, dyadicTolerance, realSeal,
        transport, replay, provenance, name]

def natRealEmbeddingToEventFlow : NatRealEmbeddingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (natRealEmbeddingFields x).map natRealEmbeddingEncodeBHist

def natRealEmbeddingFromEventFlow : EventFlow → Option NatRealEmbeddingUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | source :: rest0 =>
      match rest0 with
      | [] => none
      | rationalConstant :: rest1 =>
          match rest1 with
          | [] => none
          | constantWindows :: rest2 =>
              match rest2 with
              | [] => none
              | regularReadback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | dyadicTolerance :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (NatRealEmbeddingUp.mk
                                                  (natRealEmbeddingDecodeBHist source)
                                                  (natRealEmbeddingDecodeBHist
                                                    rationalConstant)
                                                  (natRealEmbeddingDecodeBHist constantWindows)
                                                  (natRealEmbeddingDecodeBHist regularReadback)
                                                  (natRealEmbeddingDecodeBHist dyadicTolerance)
                                                  (natRealEmbeddingDecodeBHist realSeal)
                                                  (natRealEmbeddingDecodeBHist transport)
                                                  (natRealEmbeddingDecodeBHist replay)
                                                  (natRealEmbeddingDecodeBHist provenance)
                                                  (natRealEmbeddingDecodeBHist name))
                                          | _ :: _ => none

private theorem NatRealEmbeddingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : NatRealEmbeddingUp,
      natRealEmbeddingFromEventFlow (natRealEmbeddingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk source rationalConstant constantWindows regularReadback dyadicTolerance realSeal transport
      replay provenance name =>
      change
        some
          (NatRealEmbeddingUp.mk
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist source))
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist rationalConstant))
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist constantWindows))
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist regularReadback))
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist dyadicTolerance))
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist realSeal))
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist transport))
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist replay))
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist provenance))
            (natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist name))) =
          some
            (NatRealEmbeddingUp.mk source rationalConstant constantWindows regularReadback
              dyadicTolerance realSeal transport replay provenance name)
      rw [NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode source,
        NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode rationalConstant,
        NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode constantWindows,
        NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode regularReadback,
        NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode dyadicTolerance,
        NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode realSeal,
        NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode transport,
        NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode replay,
        NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode provenance,
        NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode name]

private theorem NatRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : NatRealEmbeddingUp} :
    natRealEmbeddingToEventFlow x = natRealEmbeddingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = natRealEmbeddingFromEventFlow (natRealEmbeddingToEventFlow x) :=
        (NatRealEmbeddingTasteGate_single_carrier_alignment_round_trip x).symm
      _ = natRealEmbeddingFromEventFlow (natRealEmbeddingToEventFlow y) :=
        congrArg natRealEmbeddingFromEventFlow hxy
      _ = some y := NatRealEmbeddingTasteGate_single_carrier_alignment_round_trip y
  exact Option.some.inj optionEq

private theorem NatRealEmbeddingTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : NatRealEmbeddingUp, natRealEmbeddingFields x = natRealEmbeddingFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ rationalConstant₁ constantWindows₁ regularReadback₁ dyadicTolerance₁ realSeal₁
      transport₁ replay₁ provenance₁ name₁ =>
      cases y with
      | mk source₂ rationalConstant₂ constantWindows₂ regularReadback₂ dyadicTolerance₂
          realSeal₂ transport₂ replay₂ provenance₂ name₂ =>
          cases hfields
          rfl

instance NatRealEmbeddingTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier NatRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := natRealEmbeddingToEventFlow
  fromEventFlow := natRealEmbeddingFromEventFlow

instance NatRealEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate NatRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change natRealEmbeddingFromEventFlow (natRealEmbeddingToEventFlow x) = some x
    exact NatRealEmbeddingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NatRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance NatRealEmbeddingTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful NatRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := natRealEmbeddingFields
  field_faithful := NatRealEmbeddingTasteGate_single_carrier_alignment_field_faithful

instance NatRealEmbeddingTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial NatRealEmbeddingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NatRealEmbeddingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NatRealEmbeddingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def NatRealEmbeddingTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate NatRealEmbeddingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  NatRealEmbeddingTasteGate_single_carrier_alignment_ChapterTasteGate

theorem NatRealEmbeddingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate NatRealEmbeddingUp) ∧
      Nonempty (FieldFaithful NatRealEmbeddingUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial NatRealEmbeddingUp) ∧
      (∀ h : BHist, natRealEmbeddingDecodeBHist (natRealEmbeddingEncodeBHist h) = h) ∧
      (∀ x : NatRealEmbeddingUp,
        natRealEmbeddingFromEventFlow (natRealEmbeddingToEventFlow x) = some x) ∧
      (∀ x y : NatRealEmbeddingUp,
        natRealEmbeddingToEventFlow x = natRealEmbeddingToEventFlow y → x = y) ∧
      natRealEmbeddingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  let carrier : BHistCarrier NatRealEmbeddingUp :=
    { toEventFlow := natRealEmbeddingToEventFlow,
      fromEventFlow := natRealEmbeddingFromEventFlow }
  let chapter : @ChapterTasteGate NatRealEmbeddingUp carrier :=
    { round_trip := by
        intro x
        exact NatRealEmbeddingTasteGate_single_carrier_alignment_round_trip x,
      layer_separation := by
        intro x y hxy heq
        exact hxy (NatRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq) }
  exact
    ⟨⟨chapter⟩,
      ⟨NatRealEmbeddingTasteGate_single_carrier_alignment_FieldFaithful⟩,
      ⟨NatRealEmbeddingTasteGate_single_carrier_alignment_Nontrivial⟩,
      NatRealEmbeddingTasteGate_single_carrier_alignment_decode_encode,
      NatRealEmbeddingTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact NatRealEmbeddingTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.NatRealEmbeddingUp
