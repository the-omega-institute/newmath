import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedComparisonUp : Type where
  | mk (L R D W S E H C P N : BHist) : BishopLocatedComparisonUp
  deriving DecidableEq

def bishopLocatedComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedComparisonEncodeBHist h

def bishopLocatedComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedComparisonDecodeBHist tail)

private theorem BishopLocatedComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedComparisonFields : BishopLocatedComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedComparisonUp.mk L R D W S E H C P N => [L, R, D, W, S, E, H, C, P, N]

def bishopLocatedComparisonToEventFlow : BishopLocatedComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (bishopLocatedComparisonFields x).map bishopLocatedComparisonEncodeBHist

private def bishopLocatedComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopLocatedComparisonEventAtDefault index rest

def bishopLocatedComparisonFromEventFlow (ef : EventFlow) : Option BishopLocatedComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BishopLocatedComparisonUp.mk
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 0 ef))
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 1 ef))
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 2 ef))
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 3 ef))
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 4 ef))
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 5 ef))
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 6 ef))
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 7 ef))
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 8 ef))
      (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEventAtDefault 9 ef)))

private theorem BishopLocatedComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BishopLocatedComparisonUp,
      bishopLocatedComparisonFromEventFlow (bishopLocatedComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L R D W S E H C P N =>
      change
        some
          (BishopLocatedComparisonUp.mk
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist L))
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist R))
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist D))
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist W))
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist S))
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist E))
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist H))
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist C))
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist P))
            (bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist N))) =
          some (BishopLocatedComparisonUp.mk L R D W S E H C P N)
      rw [BishopLocatedComparisonTasteGate_single_carrier_alignment_decode L,
        BishopLocatedComparisonTasteGate_single_carrier_alignment_decode R,
        BishopLocatedComparisonTasteGate_single_carrier_alignment_decode D,
        BishopLocatedComparisonTasteGate_single_carrier_alignment_decode W,
        BishopLocatedComparisonTasteGate_single_carrier_alignment_decode S,
        BishopLocatedComparisonTasteGate_single_carrier_alignment_decode E,
        BishopLocatedComparisonTasteGate_single_carrier_alignment_decode H,
        BishopLocatedComparisonTasteGate_single_carrier_alignment_decode C,
        BishopLocatedComparisonTasteGate_single_carrier_alignment_decode P,
        BishopLocatedComparisonTasteGate_single_carrier_alignment_decode N]

private theorem bishopLocatedComparisonToEventFlow_injective
    {x y : BishopLocatedComparisonUp} :
    bishopLocatedComparisonToEventFlow x = bishopLocatedComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedComparisonFromEventFlow (bishopLocatedComparisonToEventFlow x) =
        bishopLocatedComparisonFromEventFlow (bishopLocatedComparisonToEventFlow y) :=
    congrArg bishopLocatedComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BishopLocatedComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BishopLocatedComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance bishopLocatedComparisonBHistCarrier : BHistCarrier BishopLocatedComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedComparisonToEventFlow
  fromEventFlow := bishopLocatedComparisonFromEventFlow

instance bishopLocatedComparisonChapterTasteGate :
    ChapterTasteGate BishopLocatedComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bishopLocatedComparisonFromEventFlow (bishopLocatedComparisonToEventFlow x) = some x
    exact BishopLocatedComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopLocatedComparisonToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BishopLocatedComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bishopLocatedComparisonChapterTasteGate

theorem BishopLocatedComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopLocatedComparisonDecodeBHist (bishopLocatedComparisonEncodeBHist h) = h) ∧
      (∀ x : BishopLocatedComparisonUp,
        bishopLocatedComparisonFromEventFlow (bishopLocatedComparisonToEventFlow x) = some x) ∧
      (∀ x y : BishopLocatedComparisonUp,
        bishopLocatedComparisonToEventFlow x = bishopLocatedComparisonToEventFlow y → x = y) ∧
      bishopLocatedComparisonFields (BishopLocatedComparisonUp.mk L R D W S E H C P N) =
        [L, R, D, W, S, E, H, C, P, N] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨BishopLocatedComparisonTasteGate_single_carrier_alignment_decode,
      BishopLocatedComparisonTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => bishopLocatedComparisonToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BishopLocatedComparisonUp
