import BEDC.Derived.LowerUpperRealCutUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LowerUpperRealCutUp

open BEDC.Derived
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def lowerUpperRealCutEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lowerUpperRealCutEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lowerUpperRealCutEncodeBHist h

def lowerUpperRealCutDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lowerUpperRealCutDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lowerUpperRealCutDecodeBHist tail)

private theorem LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lowerUpperRealCutFields : LowerUpperRealCutUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LowerUpperRealCutUp.mk L U G D S R E H C P N => [L, U, G, D, S, R, E, H, C, P, N]

def lowerUpperRealCutToEventFlow : LowerUpperRealCutUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lowerUpperRealCutFields x).map lowerUpperRealCutEncodeBHist

private def lowerUpperRealCutEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lowerUpperRealCutEventAtDefault index rest

def lowerUpperRealCutFromEventFlow (ef : EventFlow) : Option LowerUpperRealCutUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LowerUpperRealCutUp.mk
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 0 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 1 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 2 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 3 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 4 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 5 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 6 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 7 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 8 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 9 ef))
      (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEventAtDefault 10 ef)))

private theorem LowerUpperRealCutTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LowerUpperRealCutUp,
      lowerUpperRealCutFromEventFlow (lowerUpperRealCutToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U G D S R E H C P N =>
      change
        some
          (LowerUpperRealCutUp.mk
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist L))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist U))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist G))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist D))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist S))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist R))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist E))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist H))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist C))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist P))
            (lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist N))) =
          some (LowerUpperRealCutUp.mk L U G D S R E H C P N)
      rw [LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode L,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode U,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode G,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode D,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode S,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode R,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode E,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode H,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode C,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode P,
        LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode N]

private theorem LowerUpperRealCutTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LowerUpperRealCutUp} :
    lowerUpperRealCutToEventFlow x = lowerUpperRealCutToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lowerUpperRealCutFromEventFlow (lowerUpperRealCutToEventFlow x) =
        lowerUpperRealCutFromEventFlow (lowerUpperRealCutToEventFlow y) :=
    congrArg lowerUpperRealCutFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LowerUpperRealCutTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LowerUpperRealCutTasteGate_single_carrier_alignment_round_trip y)))

private theorem LowerUpperRealCutTasteGate_single_carrier_alignment_fields :
    ∀ x y : LowerUpperRealCutUp, lowerUpperRealCutFields x = lowerUpperRealCutFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L1 U1 G1 D1 S1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk L2 U2 G2 D2 S2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance lowerUpperRealCutBHistCarrier : BHistCarrier LowerUpperRealCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lowerUpperRealCutToEventFlow
  fromEventFlow := lowerUpperRealCutFromEventFlow

instance lowerUpperRealCutChapterTasteGate : ChapterTasteGate LowerUpperRealCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lowerUpperRealCutFromEventFlow (lowerUpperRealCutToEventFlow x) = some x
    exact LowerUpperRealCutTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LowerUpperRealCutTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance lowerUpperRealCutFieldFaithful : FieldFaithful LowerUpperRealCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lowerUpperRealCutFields
  field_faithful := LowerUpperRealCutTasteGate_single_carrier_alignment_fields

instance lowerUpperRealCutNontrivial : Nontrivial LowerUpperRealCutUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LowerUpperRealCutUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LowerUpperRealCutUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LowerUpperRealCutTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LowerUpperRealCutUp) ∧
      Nonempty (FieldFaithful LowerUpperRealCutUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LowerUpperRealCutUp) ∧
          (∀ h : BHist, lowerUpperRealCutDecodeBHist (lowerUpperRealCutEncodeBHist h) = h) ∧
            (∀ x : LowerUpperRealCutUp,
              lowerUpperRealCutFromEventFlow (lowerUpperRealCutToEventFlow x) = some x) ∧
              (∀ x y : LowerUpperRealCutUp,
                lowerUpperRealCutToEventFlow x = lowerUpperRealCutToEventFlow y → x = y) ∧
                lowerUpperRealCutEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨lowerUpperRealCutChapterTasteGate⟩,
      ⟨lowerUpperRealCutFieldFaithful⟩,
      ⟨lowerUpperRealCutNontrivial⟩,
      LowerUpperRealCutTasteGate_single_carrier_alignment_decode_encode,
      LowerUpperRealCutTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LowerUpperRealCutTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LowerUpperRealCutUp
