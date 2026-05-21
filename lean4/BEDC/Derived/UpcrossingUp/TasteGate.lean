import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UpcrossingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UpcrossingUp : Type where
  | mk
      (probability martingale lower upper horizon values lowerLedger upperLedger transport
        continuation provenance localNameCert : BHist) :
        UpcrossingUp
  deriving DecidableEq

def upcrossingEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: upcrossingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: upcrossingEncodeBHist h

def upcrossingDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (upcrossingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (upcrossingDecodeBHist tail)

private theorem UpcrossingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, upcrossingDecodeBHist (upcrossingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def upcrossingFields : UpcrossingUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UpcrossingUp.mk probability martingale lower upper horizon values lowerLedger upperLedger
      transport continuation provenance localNameCert =>
      [probability, martingale, lower, upper, horizon, values, lowerLedger, upperLedger,
        transport, continuation, provenance, localNameCert]

def upcrossingToEventFlow : UpcrossingUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (upcrossingFields x).map upcrossingEncodeBHist

private def upcrossingEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => upcrossingEventAt index rest

def upcrossingFromEventFlow : EventFlow -> Option UpcrossingUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (UpcrossingUp.mk
          (upcrossingDecodeBHist (upcrossingEventAt 0 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 1 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 2 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 3 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 4 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 5 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 6 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 7 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 8 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 9 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 10 ef))
          (upcrossingDecodeBHist (upcrossingEventAt 11 ef)))

private theorem UpcrossingTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UpcrossingUp, upcrossingFromEventFlow (upcrossingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk probability martingale lower upper horizon values lowerLedger upperLedger transport
      continuation provenance localNameCert =>
      change
        some
          (UpcrossingUp.mk
            (upcrossingDecodeBHist (upcrossingEncodeBHist probability))
            (upcrossingDecodeBHist (upcrossingEncodeBHist martingale))
            (upcrossingDecodeBHist (upcrossingEncodeBHist lower))
            (upcrossingDecodeBHist (upcrossingEncodeBHist upper))
            (upcrossingDecodeBHist (upcrossingEncodeBHist horizon))
            (upcrossingDecodeBHist (upcrossingEncodeBHist values))
            (upcrossingDecodeBHist (upcrossingEncodeBHist lowerLedger))
            (upcrossingDecodeBHist (upcrossingEncodeBHist upperLedger))
            (upcrossingDecodeBHist (upcrossingEncodeBHist transport))
            (upcrossingDecodeBHist (upcrossingEncodeBHist continuation))
            (upcrossingDecodeBHist (upcrossingEncodeBHist provenance))
            (upcrossingDecodeBHist (upcrossingEncodeBHist localNameCert))) =
          some
            (UpcrossingUp.mk probability martingale lower upper horizon values lowerLedger
              upperLedger transport continuation provenance localNameCert)
      rw [UpcrossingTasteGate_single_carrier_alignment_decode_encode probability,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode martingale,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode lower,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode upper,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode horizon,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode values,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode lowerLedger,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode upperLedger,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode transport,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode continuation,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode provenance,
        UpcrossingTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem UpcrossingTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : UpcrossingUp} :
    upcrossingToEventFlow x = upcrossingToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      upcrossingFromEventFlow (upcrossingToEventFlow x) =
        upcrossingFromEventFlow (upcrossingToEventFlow y) :=
    congrArg upcrossingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UpcrossingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UpcrossingTasteGate_single_carrier_alignment_round_trip y)))

private theorem UpcrossingTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : UpcrossingUp, upcrossingFields x = upcrossingFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk probability₁ martingale₁ lower₁ upper₁ horizon₁ values₁ lowerLedger₁ upperLedger₁
      transport₁ continuation₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk probability₂ martingale₂ lower₂ upper₂ horizon₂ values₂ lowerLedger₂ upperLedger₂
          transport₂ continuation₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance upcrossingBHistCarrier : BHistCarrier UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := upcrossingToEventFlow
  fromEventFlow := upcrossingFromEventFlow

instance upcrossingChapterTasteGate : ChapterTasteGate UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change upcrossingFromEventFlow (upcrossingToEventFlow x) = some x
    exact UpcrossingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UpcrossingTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance upcrossingFieldFaithful : FieldFaithful UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := upcrossingFields
  field_faithful := by
    intro x y h
    change upcrossingFields x = upcrossingFields y at h
    exact UpcrossingTasteGate_single_carrier_alignment_field_faithful x y h

instance upcrossingNontrivial : Nontrivial UpcrossingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨UpcrossingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      UpcrossingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem UpcrossingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate UpcrossingUp) ∧
      Nonempty (FieldFaithful UpcrossingUp) ∧
        Nonempty (Nontrivial UpcrossingUp) ∧
          (∀ h : BHist, upcrossingDecodeBHist (upcrossingEncodeBHist h) = h) ∧
            (∀ x : UpcrossingUp, upcrossingFromEventFlow (upcrossingToEventFlow x) = some x) ∧
              (∀ x y : UpcrossingUp, upcrossingToEventFlow x = upcrossingToEventFlow y -> x = y) ∧
                upcrossingEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨upcrossingChapterTasteGate⟩
  · constructor
    · exact ⟨upcrossingFieldFaithful⟩
    · constructor
      · exact ⟨upcrossingNontrivial⟩
      · constructor
        · exact UpcrossingTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact UpcrossingTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact UpcrossingTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.UpcrossingUp.TasteGate
