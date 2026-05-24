import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AbelLimitTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AbelLimitTheoremUp : Type where
  | mk :
      (abel source limit uniform regular realSeal transport continuation provenance localNameCert :
        BHist) ->
        AbelLimitTheoremUp
  deriving DecidableEq

def abelLimitTheoremEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: abelLimitTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: abelLimitTheoremEncodeBHist h

def abelLimitTheoremDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (abelLimitTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (abelLimitTheoremDecodeBHist tail)

theorem AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def abelLimitTheoremFields : AbelLimitTheoremUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AbelLimitTheoremUp.mk abel source limit uniform regular realSeal transport continuation
      provenance localNameCert =>
      [abel, source, limit, uniform, regular, realSeal, transport, continuation, provenance,
        localNameCert]

def abelLimitTheoremToEventFlow : AbelLimitTheoremUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (abelLimitTheoremFields x).map abelLimitTheoremEncodeBHist

def abelLimitTheoremFromEventFlow : EventFlow -> Option AbelLimitTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | abel :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | limit :: rest2 =>
              match rest2 with
              | [] => none
              | uniform :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regular :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | continuation :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localNameCert :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (AbelLimitTheoremUp.mk
                                                  (abelLimitTheoremDecodeBHist abel)
                                                  (abelLimitTheoremDecodeBHist source)
                                                  (abelLimitTheoremDecodeBHist limit)
                                                  (abelLimitTheoremDecodeBHist uniform)
                                                  (abelLimitTheoremDecodeBHist regular)
                                                  (abelLimitTheoremDecodeBHist realSeal)
                                                  (abelLimitTheoremDecodeBHist transport)
                                                  (abelLimitTheoremDecodeBHist continuation)
                                                  (abelLimitTheoremDecodeBHist provenance)
                                                  (abelLimitTheoremDecodeBHist localNameCert))
                                          | _ :: _ => none

theorem AbelLimitTheoremTasteGate_single_carrier_alignment_round_trip :
    forall x : AbelLimitTheoremUp,
      abelLimitTheoremFromEventFlow (abelLimitTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk abel source limit uniform regular realSeal transport continuation provenance localNameCert =>
      change
        some
          (AbelLimitTheoremUp.mk
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist abel))
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist source))
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist limit))
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist uniform))
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist regular))
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist realSeal))
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist transport))
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist continuation))
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist provenance))
            (abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist localNameCert))) =
          some
            (AbelLimitTheoremUp.mk abel source limit uniform regular realSeal transport
              continuation provenance localNameCert)
      rw [AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode abel,
        AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode source,
        AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode limit,
        AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode uniform,
        AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode regular,
        AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode realSeal,
        AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode transport,
        AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode continuation,
        AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode provenance,
        AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode localNameCert]

theorem AbelLimitTheoremTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : AbelLimitTheoremUp} :
    abelLimitTheoremToEventFlow x = abelLimitTheoremToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      abelLimitTheoremFromEventFlow (abelLimitTheoremToEventFlow x) =
        abelLimitTheoremFromEventFlow (abelLimitTheoremToEventFlow y) :=
    congrArg abelLimitTheoremFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (AbelLimitTheoremTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (AbelLimitTheoremTasteGate_single_carrier_alignment_round_trip y)))

theorem AbelLimitTheoremTasteGate_single_carrier_alignment_field_faithful :
    forall x y : AbelLimitTheoremUp, abelLimitTheoremFields x = abelLimitTheoremFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk abel₁ source₁ limit₁ uniform₁ regular₁ realSeal₁ transport₁ continuation₁ provenance₁
      localNameCert₁ =>
      cases y with
      | mk abel₂ source₂ limit₂ uniform₂ regular₂ realSeal₂ transport₂ continuation₂ provenance₂
          localNameCert₂ =>
          cases hfields
          rfl

instance abelLimitTheoremBHistCarrier : BHistCarrier AbelLimitTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := abelLimitTheoremToEventFlow
  fromEventFlow := abelLimitTheoremFromEventFlow

instance abelLimitTheoremChapterTasteGate : ChapterTasteGate AbelLimitTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := fun x =>
    id (AbelLimitTheoremTasteGate_single_carrier_alignment_round_trip x)
  layer_separation := by
    intro x y hxy heq
    exact hxy (AbelLimitTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance abelLimitTheoremFieldFaithful : FieldFaithful AbelLimitTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := abelLimitTheoremFields
  field_faithful := AbelLimitTheoremTasteGate_single_carrier_alignment_field_faithful

instance abelLimitTheoremNontrivial :
    BEDC.Meta.TasteGate.Nontrivial AbelLimitTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AbelLimitTheoremUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AbelLimitTheoremUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def abelLimitTheoremTasteGate : ChapterTasteGate AbelLimitTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  abelLimitTheoremChapterTasteGate

theorem AbelLimitTheoremTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate AbelLimitTheoremUp) ∧
      Nonempty (FieldFaithful AbelLimitTheoremUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial AbelLimitTheoremUp) ∧
          (∀ h : BHist, abelLimitTheoremDecodeBHist (abelLimitTheoremEncodeBHist h) = h) ∧
            (∀ x : AbelLimitTheoremUp,
              abelLimitTheoremFromEventFlow (abelLimitTheoremToEventFlow x) = some x) ∧
              (∀ x y : AbelLimitTheoremUp,
                abelLimitTheoremToEventFlow x = abelLimitTheoremToEventFlow y -> x = y) ∧
                abelLimitTheoremEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨abelLimitTheoremChapterTasteGate⟩
  · constructor
    · exact ⟨abelLimitTheoremFieldFaithful⟩
    · constructor
      · exact ⟨abelLimitTheoremNontrivial⟩
      · constructor
        · exact AbelLimitTheoremTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact AbelLimitTheoremTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact AbelLimitTheoremTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.AbelLimitTheoremUp
