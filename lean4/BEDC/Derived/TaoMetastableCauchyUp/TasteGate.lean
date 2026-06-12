import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TaoMetastableCauchyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TaoMetastableCauchyUp : Type where
  | mk (q F W D S R E B H C P N : BHist) : TaoMetastableCauchyUp
  deriving DecidableEq

def taoMetastableCauchyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: taoMetastableCauchyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: taoMetastableCauchyEncodeBHist h

def taoMetastableCauchyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (taoMetastableCauchyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (taoMetastableCauchyDecodeBHist tail)

private theorem TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def taoMetastableCauchyFields : TaoMetastableCauchyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TaoMetastableCauchyUp.mk q F W D S R E B H C P N => [q, F, W, D, S, R, E, B, H, C, P, N]

def taoMetastableCauchyToEventFlow : TaoMetastableCauchyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (taoMetastableCauchyFields x).map taoMetastableCauchyEncodeBHist

private def taoMetastableCauchyEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => taoMetastableCauchyEventAt index rest

def taoMetastableCauchyFromEventFlow (ef : EventFlow) :
    Option TaoMetastableCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TaoMetastableCauchyUp.mk
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 0 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 1 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 2 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 3 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 4 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 5 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 6 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 7 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 8 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 9 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 10 ef))
      (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEventAt 11 ef)))

private theorem TaoMetastableCauchyTasteGate_single_carrier_alignment_round_trip
    (x : TaoMetastableCauchyUp) :
    taoMetastableCauchyFromEventFlow (taoMetastableCauchyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk q F W D S R E B H C P N =>
      change
        some
          (TaoMetastableCauchyUp.mk
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist q))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist F))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist W))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist D))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist S))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist R))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist E))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist B))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist H))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist C))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist P))
            (taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist N))) =
          some (TaoMetastableCauchyUp.mk q F W D S R E B H C P N)
      rw [TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode q,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode F,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode W,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode D,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode S,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode R,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode E,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode B,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode H,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode C,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode P,
        TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode N]

private theorem TaoMetastableCauchyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TaoMetastableCauchyUp} :
    taoMetastableCauchyToEventFlow x = taoMetastableCauchyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      taoMetastableCauchyFromEventFlow (taoMetastableCauchyToEventFlow x) =
        taoMetastableCauchyFromEventFlow (taoMetastableCauchyToEventFlow y) :=
    congrArg taoMetastableCauchyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TaoMetastableCauchyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TaoMetastableCauchyTasteGate_single_carrier_alignment_round_trip y)))

private theorem TaoMetastableCauchyTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : TaoMetastableCauchyUp,
      taoMetastableCauchyFields x = taoMetastableCauchyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk q1 F1 W1 D1 S1 R1 E1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk q2 F2 W2 D2 S2 R2 E2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance taoMetastableCauchyBHistCarrier : BHistCarrier TaoMetastableCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := taoMetastableCauchyToEventFlow
  fromEventFlow := taoMetastableCauchyFromEventFlow

instance taoMetastableCauchyChapterTasteGate :
    ChapterTasteGate TaoMetastableCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change taoMetastableCauchyFromEventFlow (taoMetastableCauchyToEventFlow x) = some x
    exact TaoMetastableCauchyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TaoMetastableCauchyTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance taoMetastableCauchyFieldFaithful :
    FieldFaithful TaoMetastableCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := taoMetastableCauchyFields
  field_faithful := TaoMetastableCauchyTasteGate_single_carrier_alignment_fields_faithful

instance taoMetastableCauchyNontrivial : Nontrivial TaoMetastableCauchyUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TaoMetastableCauchyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      TaoMetastableCauchyUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def TaoMetastableCauchyTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate TaoMetastableCauchyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  taoMetastableCauchyChapterTasteGate

theorem TaoMetastableCauchyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      taoMetastableCauchyDecodeBHist (taoMetastableCauchyEncodeBHist h) = h) ∧
      (∀ x : TaoMetastableCauchyUp,
        taoMetastableCauchyFromEventFlow (taoMetastableCauchyToEventFlow x) = some x) ∧
        (∀ x y : TaoMetastableCauchyUp,
          taoMetastableCauchyToEventFlow x = taoMetastableCauchyToEventFlow y → x = y) ∧
          taoMetastableCauchyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨TaoMetastableCauchyTasteGate_single_carrier_alignment_decode_encode,
      TaoMetastableCauchyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        TaoMetastableCauchyTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.TaoMetastableCauchyUp
