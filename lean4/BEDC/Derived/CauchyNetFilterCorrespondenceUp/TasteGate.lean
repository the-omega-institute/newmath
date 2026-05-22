import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyNetFilterCorrespondenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyNetFilterCorrespondenceUp : Type where
  | mk (K F U W R E J H C P N : BHist) : CauchyNetFilterCorrespondenceUp
  deriving DecidableEq

def cauchyNetFilterCorrespondenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyNetFilterCorrespondenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyNetFilterCorrespondenceEncodeBHist h

def cauchyNetFilterCorrespondenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyNetFilterCorrespondenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyNetFilterCorrespondenceDecodeBHist tail)

private theorem CauchyNetFilterCorrespondenceTasteGate_decode_encode :
    ∀ h : BHist,
      cauchyNetFilterCorrespondenceDecodeBHist
        (cauchyNetFilterCorrespondenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyNetFilterCorrespondenceToEventFlow :
    CauchyNetFilterCorrespondenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetFilterCorrespondenceUp.mk K F U W R E J H C P N =>
      [cauchyNetFilterCorrespondenceEncodeBHist K,
        cauchyNetFilterCorrespondenceEncodeBHist F,
        cauchyNetFilterCorrespondenceEncodeBHist U,
        cauchyNetFilterCorrespondenceEncodeBHist W,
        cauchyNetFilterCorrespondenceEncodeBHist R,
        cauchyNetFilterCorrespondenceEncodeBHist E,
        cauchyNetFilterCorrespondenceEncodeBHist J,
        cauchyNetFilterCorrespondenceEncodeBHist H,
        cauchyNetFilterCorrespondenceEncodeBHist C,
        cauchyNetFilterCorrespondenceEncodeBHist P,
        cauchyNetFilterCorrespondenceEncodeBHist N]

def cauchyNetFilterCorrespondenceFields :
    CauchyNetFilterCorrespondenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyNetFilterCorrespondenceUp.mk K F U W R E J H C P N =>
      [K, F, U, W, R, E, J, H, C, P, N]

private def cauchyNetFilterCorrespondenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyNetFilterCorrespondenceEventAtDefault index rest

def cauchyNetFilterCorrespondenceFromEventFlow :
    EventFlow → Option CauchyNetFilterCorrespondenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchyNetFilterCorrespondenceUp.mk
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 0 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 1 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 2 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 3 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 4 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 5 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 6 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 7 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 8 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 9 ef))
          (cauchyNetFilterCorrespondenceDecodeBHist
            (cauchyNetFilterCorrespondenceEventAtDefault 10 ef)))

private theorem CauchyNetFilterCorrespondenceTasteGate_round_trip
    (x : CauchyNetFilterCorrespondenceUp) :
    cauchyNetFilterCorrespondenceFromEventFlow
      (cauchyNetFilterCorrespondenceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk K F U W R E J H C P N =>
      change
        some
          (CauchyNetFilterCorrespondenceUp.mk
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist K))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist F))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist U))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist W))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist R))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist E))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist J))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist H))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist C))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist P))
            (cauchyNetFilterCorrespondenceDecodeBHist
              (cauchyNetFilterCorrespondenceEncodeBHist N))) =
          some (CauchyNetFilterCorrespondenceUp.mk K F U W R E J H C P N)
      rw [CauchyNetFilterCorrespondenceTasteGate_decode_encode K,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode F,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode U,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode W,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode R,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode E,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode J,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode H,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode C,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode P,
        CauchyNetFilterCorrespondenceTasteGate_decode_encode N]

private theorem CauchyNetFilterCorrespondenceTasteGate_toEventFlow_injective
    {x y : CauchyNetFilterCorrespondenceUp} :
    cauchyNetFilterCorrespondenceToEventFlow x =
      cauchyNetFilterCorrespondenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyNetFilterCorrespondenceFromEventFlow
          (cauchyNetFilterCorrespondenceToEventFlow x) =
        cauchyNetFilterCorrespondenceFromEventFlow
          (cauchyNetFilterCorrespondenceToEventFlow y) :=
    congrArg cauchyNetFilterCorrespondenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyNetFilterCorrespondenceTasteGate_round_trip x).symm
      (Eq.trans hread (CauchyNetFilterCorrespondenceTasteGate_round_trip y)))

private theorem CauchyNetFilterCorrespondenceTasteGate_fields_faithful :
    ∀ x y : CauchyNetFilterCorrespondenceUp,
      cauchyNetFilterCorrespondenceFields x =
        cauchyNetFilterCorrespondenceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 F1 U1 W1 R1 E1 J1 H1 C1 P1 N1 =>
      cases y with
      | mk K2 F2 U2 W2 R2 E2 J2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyNetFilterCorrespondenceBHistCarrier :
    BHistCarrier CauchyNetFilterCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyNetFilterCorrespondenceToEventFlow
  fromEventFlow := cauchyNetFilterCorrespondenceFromEventFlow

instance cauchyNetFilterCorrespondenceChapterTasteGate :
    ChapterTasteGate CauchyNetFilterCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := CauchyNetFilterCorrespondenceTasteGate_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyNetFilterCorrespondenceTasteGate_toEventFlow_injective heq)

instance cauchyNetFilterCorrespondenceFieldFaithful :
    FieldFaithful CauchyNetFilterCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyNetFilterCorrespondenceFields
  field_faithful := CauchyNetFilterCorrespondenceTasteGate_fields_faithful

instance cauchyNetFilterCorrespondenceNontrivial :
    Nontrivial CauchyNetFilterCorrespondenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyNetFilterCorrespondenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CauchyNetFilterCorrespondenceUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyNetFilterCorrespondenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyNetFilterCorrespondenceChapterTasteGate

theorem CauchyNetFilterCorrespondenceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyNetFilterCorrespondenceDecodeBHist
        (cauchyNetFilterCorrespondenceEncodeBHist h) = h) ∧
      (∀ x : CauchyNetFilterCorrespondenceUp,
        cauchyNetFilterCorrespondenceFromEventFlow
          (cauchyNetFilterCorrespondenceToEventFlow x) = some x) ∧
        (∀ x y : CauchyNetFilterCorrespondenceUp,
          cauchyNetFilterCorrespondenceToEventFlow x =
            cauchyNetFilterCorrespondenceToEventFlow y → x = y) ∧
          cauchyNetFilterCorrespondenceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyNetFilterCorrespondenceTasteGate_decode_encode,
      CauchyNetFilterCorrespondenceTasteGate_round_trip,
      (fun _ _ heq => CauchyNetFilterCorrespondenceTasteGate_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyNetFilterCorrespondenceUp
