import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyFilterNetCorrespondenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyFilterNetCorrespondenceUp : Type where
  | mk (F D W R T M U H C P N : BHist) : CauchyFilterNetCorrespondenceUp
  deriving DecidableEq

def cauchyFilterNetCorrespondenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyFilterNetCorrespondenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyFilterNetCorrespondenceEncodeBHist h

def cauchyFilterNetCorrespondenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyFilterNetCorrespondenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyFilterNetCorrespondenceDecodeBHist tail)

private theorem CauchyFilterNetCorrespondenceTasteGate_decode_encode :
    ∀ h : BHist,
      cauchyFilterNetCorrespondenceDecodeBHist
        (cauchyFilterNetCorrespondenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyFilterNetCorrespondenceToEventFlow :
    CauchyFilterNetCorrespondenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterNetCorrespondenceUp.mk F D W R T M U H C P N =>
      [cauchyFilterNetCorrespondenceEncodeBHist F,
        cauchyFilterNetCorrespondenceEncodeBHist D,
        cauchyFilterNetCorrespondenceEncodeBHist W,
        cauchyFilterNetCorrespondenceEncodeBHist R,
        cauchyFilterNetCorrespondenceEncodeBHist T,
        cauchyFilterNetCorrespondenceEncodeBHist M,
        cauchyFilterNetCorrespondenceEncodeBHist U,
        cauchyFilterNetCorrespondenceEncodeBHist H,
        cauchyFilterNetCorrespondenceEncodeBHist C,
        cauchyFilterNetCorrespondenceEncodeBHist P,
        cauchyFilterNetCorrespondenceEncodeBHist N]

private def cauchyFilterNetCorrespondenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyFilterNetCorrespondenceEventAtDefault index rest

def cauchyFilterNetCorrespondenceFromEventFlow :
    EventFlow → Option CauchyFilterNetCorrespondenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyFilterNetCorrespondenceUp.mk
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 0 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 1 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 2 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 3 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 4 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 5 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 6 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 7 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 8 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 9 ef))
          (cauchyFilterNetCorrespondenceDecodeBHist
            (cauchyFilterNetCorrespondenceEventAtDefault 10 ef)))

private theorem CauchyFilterNetCorrespondenceTasteGate_round_trip
    (x : CauchyFilterNetCorrespondenceUp) :
    cauchyFilterNetCorrespondenceFromEventFlow
      (cauchyFilterNetCorrespondenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F D W R T M U H C P N =>
      change
        some
          (CauchyFilterNetCorrespondenceUp.mk
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist F))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist D))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist W))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist R))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist T))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist M))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist U))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist H))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist C))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist P))
            (cauchyFilterNetCorrespondenceDecodeBHist
              (cauchyFilterNetCorrespondenceEncodeBHist N))) =
          some (CauchyFilterNetCorrespondenceUp.mk F D W R T M U H C P N)
      rw [CauchyFilterNetCorrespondenceTasteGate_decode_encode F,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode D,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode W,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode R,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode T,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode M,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode U,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode H,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode C,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode P,
        CauchyFilterNetCorrespondenceTasteGate_decode_encode N]

private theorem CauchyFilterNetCorrespondenceTasteGate_toEventFlow_injective
    {x y : CauchyFilterNetCorrespondenceUp} :
    cauchyFilterNetCorrespondenceToEventFlow x =
      cauchyFilterNetCorrespondenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyFilterNetCorrespondenceFromEventFlow
          (cauchyFilterNetCorrespondenceToEventFlow x) =
        cauchyFilterNetCorrespondenceFromEventFlow
          (cauchyFilterNetCorrespondenceToEventFlow y) :=
    congrArg cauchyFilterNetCorrespondenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyFilterNetCorrespondenceTasteGate_round_trip x).symm
      (Eq.trans hread (CauchyFilterNetCorrespondenceTasteGate_round_trip y)))

def CauchyFilterNetCorrespondenceTasteGate_single_carrier_alignment_fields :
    CauchyFilterNetCorrespondenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyFilterNetCorrespondenceUp.mk F D W R T M U H C P N =>
      [F, D, W, R, T, M, U, H, C, P, N]

private theorem CauchyFilterNetCorrespondenceTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CauchyFilterNetCorrespondenceUp,
      CauchyFilterNetCorrespondenceTasteGate_single_carrier_alignment_fields x =
        CauchyFilterNetCorrespondenceTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  intro x y hfields
  cases x with
  | mk F D W R T M U H C P N =>
      cases y with
      | mk F' D' W' R' T' M' U' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyFilterNetCorrespondenceBHistCarrier :
    BHistCarrier CauchyFilterNetCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyFilterNetCorrespondenceToEventFlow
  fromEventFlow := cauchyFilterNetCorrespondenceFromEventFlow

instance cauchyFilterNetCorrespondenceChapterTasteGate :
    ChapterTasteGate CauchyFilterNetCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := CauchyFilterNetCorrespondenceTasteGate_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyFilterNetCorrespondenceTasteGate_toEventFlow_injective heq)

instance cauchyFilterNetCorrespondenceFieldFaithful :
    FieldFaithful CauchyFilterNetCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  fields := CauchyFilterNetCorrespondenceTasteGate_single_carrier_alignment_fields
  field_faithful := CauchyFilterNetCorrespondenceTasteGate_single_carrier_alignment_field_faithful

def taste_gate : ChapterTasteGate CauchyFilterNetCorrespondenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyFilterNetCorrespondenceChapterTasteGate

theorem CauchyFilterNetCorrespondenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyFilterNetCorrespondenceDecodeBHist
        (cauchyFilterNetCorrespondenceEncodeBHist h) = h) ∧
      (∀ x : CauchyFilterNetCorrespondenceUp,
        cauchyFilterNetCorrespondenceFromEventFlow
          (cauchyFilterNetCorrespondenceToEventFlow x) = some x) ∧
        (∀ x y : CauchyFilterNetCorrespondenceUp,
          cauchyFilterNetCorrespondenceToEventFlow x =
            cauchyFilterNetCorrespondenceToEventFlow y → x = y) ∧
          cauchyFilterNetCorrespondenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyFilterNetCorrespondenceTasteGate_decode_encode,
      CauchyFilterNetCorrespondenceTasteGate_round_trip,
      (fun _ _ heq => CauchyFilterNetCorrespondenceTasteGate_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyFilterNetCorrespondenceUp
