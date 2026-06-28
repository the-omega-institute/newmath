import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

namespace TasteGate

inductive BishopLocatedRealUp : Type where
  | mk (D S R I A B E H C P N : BHist) : BishopLocatedRealUp
  deriving DecidableEq

def bishopLocatedRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedRealEncodeBHist h

def bishopLocatedRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedRealDecodeBHist tail)

private theorem BishopLocatedRealTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedRealFields : BishopLocatedRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedRealUp.mk D S R I A B E H C P N => [D, S, R, I, A, B, E, H, C, P, N]

def bishopLocatedRealToEventFlow : BishopLocatedRealUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopLocatedRealFields x).map bishopLocatedRealEncodeBHist

private def bishopLocatedRealEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedRealEventAtDefault index rest

def bishopLocatedRealFromEventFlow (ef : EventFlow) : Option BishopLocatedRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedRealUp.mk
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 0 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 1 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 2 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 3 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 4 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 5 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 6 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 7 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 8 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 9 ef))
      (bishopLocatedRealDecodeBHist (bishopLocatedRealEventAtDefault 10 ef)))

private theorem BishopLocatedRealTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedRealUp,
      bishopLocatedRealFromEventFlow (bishopLocatedRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R I A B E H C P N =>
      change
        some
          (BishopLocatedRealUp.mk
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist D))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist S))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist R))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist I))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist A))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist B))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist E))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist H))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist C))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist P))
            (bishopLocatedRealDecodeBHist (bishopLocatedRealEncodeBHist N))) =
          some (BishopLocatedRealUp.mk D S R I A B E H C P N)
      rw [BishopLocatedRealTasteGate_single_carrier_alignment_decode D,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode S,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode R,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode I,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode A,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode B,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode E,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode H,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode C,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode P,
        BishopLocatedRealTasteGate_single_carrier_alignment_decode N]

private theorem BishopLocatedRealTasteGate_single_carrier_alignment_injective
    {x y : BishopLocatedRealUp} :
    bishopLocatedRealToEventFlow x = bishopLocatedRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedRealFromEventFlow (bishopLocatedRealToEventFlow x) =
        bishopLocatedRealFromEventFlow (bishopLocatedRealToEventFlow y) :=
    congrArg bishopLocatedRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopLocatedRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopLocatedRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem BishopLocatedRealTasteGate_single_carrier_alignment_fields :
    ∀ x y : BishopLocatedRealUp, bishopLocatedRealFields x = bishopLocatedRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 S1 R1 I1 A1 B1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk D2 S2 R2 I2 A2 B2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bishopLocatedRealBHistCarrier : BHistCarrier BishopLocatedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedRealToEventFlow
  fromEventFlow := bishopLocatedRealFromEventFlow

instance bishopLocatedRealChapterTasteGate : ChapterTasteGate BishopLocatedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopLocatedRealFromEventFlow (bishopLocatedRealToEventFlow x) = some x
    exact BishopLocatedRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BishopLocatedRealTasteGate_single_carrier_alignment_injective heq)

instance bishopLocatedRealFieldFaithful : FieldFaithful BishopLocatedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bishopLocatedRealFields
  field_faithful := BishopLocatedRealTasteGate_single_carrier_alignment_fields

instance bishopLocatedRealNontrivial : Nontrivial BishopLocatedRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BishopLocatedRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BishopLocatedRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

end TasteGate

theorem BishopLocatedRealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      TasteGate.bishopLocatedRealDecodeBHist (TasteGate.bishopLocatedRealEncodeBHist h) = h) ∧
      (∀ x : TasteGate.BishopLocatedRealUp,
        TasteGate.bishopLocatedRealFromEventFlow (TasteGate.bishopLocatedRealToEventFlow x) =
          some x) ∧
        (∀ x y : TasteGate.BishopLocatedRealUp,
          TasteGate.bishopLocatedRealToEventFlow x =
            TasteGate.bishopLocatedRealToEventFlow y →
            x = y) ∧
          TasteGate.bishopLocatedRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨TasteGate.BishopLocatedRealTasteGate_single_carrier_alignment_decode,
      TasteGate.BishopLocatedRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => TasteGate.BishopLocatedRealTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.BishopLocatedRealUp
