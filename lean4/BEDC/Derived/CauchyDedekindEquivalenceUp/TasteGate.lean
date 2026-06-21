import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDedekindEquivalenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDedekindEquivalenceUp : Type where
  | mk (R W D L B E0 H C P N : BHist) : CauchyDedekindEquivalenceUp
  deriving DecidableEq

def cauchyDedekindEquivalenceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDedekindEquivalenceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDedekindEquivalenceEncodeBHist h

def cauchyDedekindEquivalenceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDedekindEquivalenceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDedekindEquivalenceDecodeBHist tail)

private theorem CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyDedekindEquivalenceDecodeBHist
        (cauchyDedekindEquivalenceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_fields :
    CauchyDedekindEquivalenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDedekindEquivalenceUp.mk R W D L B E0 H C P N =>
      [R, W, D, L, B, E0, H, C, P, N]

def cauchyDedekindEquivalenceToEventFlow :
    CauchyDedekindEquivalenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token =>
      (CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_fields token).map
        cauchyDedekindEquivalenceEncodeBHist

private def cauchyDedekindEquivalenceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyDedekindEquivalenceEventAtDefault index rest

def cauchyDedekindEquivalenceFromEventFlow
    (ef : EventFlow) : Option CauchyDedekindEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyDedekindEquivalenceUp.mk
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 0 ef))
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 1 ef))
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 2 ef))
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 3 ef))
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 4 ef))
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 5 ef))
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 6 ef))
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 7 ef))
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 8 ef))
      (cauchyDedekindEquivalenceDecodeBHist (cauchyDedekindEquivalenceEventAtDefault 9 ef)))

private theorem cauchyDedekindEquivalence_round_trip :
    ∀ token : CauchyDedekindEquivalenceUp,
      cauchyDedekindEquivalenceFromEventFlow
        (cauchyDedekindEquivalenceToEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk R W D L B E0 H C P N =>
      change
        some
          (CauchyDedekindEquivalenceUp.mk
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist R))
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist W))
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist D))
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist L))
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist B))
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist E0))
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist H))
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist C))
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist P))
            (cauchyDedekindEquivalenceDecodeBHist
              (cauchyDedekindEquivalenceEncodeBHist N))) =
          some (CauchyDedekindEquivalenceUp.mk R W D L B E0 H C P N)
      rw [CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode R,
        CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode W,
        CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode D,
        CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode L,
        CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode B,
        CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode E0,
        CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode H,
        CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode C,
        CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode P,
        CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode N]

private theorem cauchyDedekindEquivalenceToEventFlow_injective
    {x y : CauchyDedekindEquivalenceUp} :
    cauchyDedekindEquivalenceToEventFlow x =
      cauchyDedekindEquivalenceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDedekindEquivalenceFromEventFlow
          (cauchyDedekindEquivalenceToEventFlow x) =
        cauchyDedekindEquivalenceFromEventFlow
          (cauchyDedekindEquivalenceToEventFlow y) :=
    congrArg cauchyDedekindEquivalenceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyDedekindEquivalence_round_trip x).symm
      (Eq.trans hread (cauchyDedekindEquivalence_round_trip y)))

private theorem cauchyDedekindEquivalence_fields_faithful
    {x y : CauchyDedekindEquivalenceUp} :
    CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_fields x =
      CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hfields
  cases x with
  | mk R1 W1 D1 L1 B1 E01 H1 C1 P1 N1 =>
      cases y with
      | mk R2 W2 D2 L2 B2 E02 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyDedekindEquivalenceBHistCarrier :
    BHistCarrier CauchyDedekindEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDedekindEquivalenceToEventFlow
  fromEventFlow := cauchyDedekindEquivalenceFromEventFlow

instance cauchyDedekindEquivalenceChapterTasteGate :
    ChapterTasteGate CauchyDedekindEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyDedekindEquivalenceFromEventFlow
        (cauchyDedekindEquivalenceToEventFlow x) = some x
    exact cauchyDedekindEquivalence_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyDedekindEquivalenceToEventFlow_injective heq)

instance cauchyDedekindEquivalenceFieldFaithful :
    FieldFaithful CauchyDedekindEquivalenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_fields
  field_faithful := by
    intro x y h
    exact cauchyDedekindEquivalence_fields_faithful h

def taste_gate : ChapterTasteGate CauchyDedekindEquivalenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyDedekindEquivalenceChapterTasteGate

theorem CauchyDedekindEquivalenceTasteGate_single_carrier_alignment :
    (∀ R W D L B E0 H C P N : BHist,
      CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_fields
          (CauchyDedekindEquivalenceUp.mk R W D L B E0 H C P N) =
        [R, W, D, L, B, E0, H, C, P, N]) ∧
      (∀ h : BHist,
        cauchyDedekindEquivalenceDecodeBHist
          (cauchyDedekindEquivalenceEncodeBHist h) = h) ∧
        cauchyDedekindEquivalenceEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  exact
    ⟨(by
        intro R W D L B E0 H C P N
        rfl),
      CauchyDedekindEquivalenceTasteGate_single_carrier_alignment_decode_encode,
      rfl⟩

end BEDC.Derived.CauchyDedekindEquivalenceUp
