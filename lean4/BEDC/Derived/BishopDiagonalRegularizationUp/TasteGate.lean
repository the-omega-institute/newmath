import BEDC.Derived.BishopDiagonalRegularizationUp
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopDiagonalRegularizationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def bishopDiagonalRegularizationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopDiagonalRegularizationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopDiagonalRegularizationEncodeBHist h

def bishopDiagonalRegularizationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopDiagonalRegularizationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopDiagonalRegularizationDecodeBHist tail)

private theorem BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      bishopDiagonalRegularizationDecodeBHist
          (bishopDiagonalRegularizationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopDiagonalRegularizationFields :
    _root_.BEDC.Derived.BishopDiagonalRegularizationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.BishopDiagonalRegularizationUp.mk
      M W D R E H C P N => [M, W, D, R, E, H, C, P, N]

def bishopDiagonalRegularizationToEventFlow :
    _root_.BEDC.Derived.BishopDiagonalRegularizationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopDiagonalRegularizationFields x).map
      bishopDiagonalRegularizationEncodeBHist

private def bishopDiagonalRegularizationEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bishopDiagonalRegularizationEventAtDefault index rest

def bishopDiagonalRegularizationFromEventFlow (ef : EventFlow) :
    Option _root_.BEDC.Derived.BishopDiagonalRegularizationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (_root_.BEDC.Derived.BishopDiagonalRegularizationUp.mk
      (bishopDiagonalRegularizationDecodeBHist
        (bishopDiagonalRegularizationEventAtDefault 0 ef))
      (bishopDiagonalRegularizationDecodeBHist
        (bishopDiagonalRegularizationEventAtDefault 1 ef))
      (bishopDiagonalRegularizationDecodeBHist
        (bishopDiagonalRegularizationEventAtDefault 2 ef))
      (bishopDiagonalRegularizationDecodeBHist
        (bishopDiagonalRegularizationEventAtDefault 3 ef))
      (bishopDiagonalRegularizationDecodeBHist
        (bishopDiagonalRegularizationEventAtDefault 4 ef))
      (bishopDiagonalRegularizationDecodeBHist
        (bishopDiagonalRegularizationEventAtDefault 5 ef))
      (bishopDiagonalRegularizationDecodeBHist
        (bishopDiagonalRegularizationEventAtDefault 6 ef))
      (bishopDiagonalRegularizationDecodeBHist
        (bishopDiagonalRegularizationEventAtDefault 7 ef))
      (bishopDiagonalRegularizationDecodeBHist
        (bishopDiagonalRegularizationEventAtDefault 8 ef)))

private theorem BishopDiagonalRegularizationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : _root_.BEDC.Derived.BishopDiagonalRegularizationUp,
      bishopDiagonalRegularizationFromEventFlow
          (bishopDiagonalRegularizationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M W D R E H C P N =>
      change
        some
            (_root_.BEDC.Derived.BishopDiagonalRegularizationUp.mk
              (bishopDiagonalRegularizationDecodeBHist
                (bishopDiagonalRegularizationEncodeBHist M))
              (bishopDiagonalRegularizationDecodeBHist
                (bishopDiagonalRegularizationEncodeBHist W))
              (bishopDiagonalRegularizationDecodeBHist
                (bishopDiagonalRegularizationEncodeBHist D))
              (bishopDiagonalRegularizationDecodeBHist
                (bishopDiagonalRegularizationEncodeBHist R))
              (bishopDiagonalRegularizationDecodeBHist
                (bishopDiagonalRegularizationEncodeBHist E))
              (bishopDiagonalRegularizationDecodeBHist
                (bishopDiagonalRegularizationEncodeBHist H))
              (bishopDiagonalRegularizationDecodeBHist
                (bishopDiagonalRegularizationEncodeBHist C))
              (bishopDiagonalRegularizationDecodeBHist
                (bishopDiagonalRegularizationEncodeBHist P))
              (bishopDiagonalRegularizationDecodeBHist
                (bishopDiagonalRegularizationEncodeBHist N))) =
          some (_root_.BEDC.Derived.BishopDiagonalRegularizationUp.mk
            M W D R E H C P N)
      rw [BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode M,
        BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode W,
        BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode D,
        BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode R,
        BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode E,
        BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode H,
        BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode C,
        BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode P,
        BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode N]

private theorem BishopDiagonalRegularizationTasteGate_single_carrier_alignment_injective
    {x y : _root_.BEDC.Derived.BishopDiagonalRegularizationUp} :
    bishopDiagonalRegularizationToEventFlow x =
      bishopDiagonalRegularizationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopDiagonalRegularizationFromEventFlow
          (bishopDiagonalRegularizationToEventFlow x) =
        bishopDiagonalRegularizationFromEventFlow
          (bishopDiagonalRegularizationToEventFlow y) :=
    congrArg bishopDiagonalRegularizationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BishopDiagonalRegularizationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BishopDiagonalRegularizationTasteGate_single_carrier_alignment_round_trip y)))

instance bishopDiagonalRegularizationBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.BishopDiagonalRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopDiagonalRegularizationToEventFlow
  fromEventFlow := bishopDiagonalRegularizationFromEventFlow

instance bishopDiagonalRegularizationChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.BishopDiagonalRegularizationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopDiagonalRegularizationFromEventFlow
          (bishopDiagonalRegularizationToEventFlow x) = some x
    exact BishopDiagonalRegularizationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (BishopDiagonalRegularizationTasteGate_single_carrier_alignment_injective heq)

theorem BishopDiagonalRegularizationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bishopDiagonalRegularizationDecodeBHist
          (bishopDiagonalRegularizationEncodeBHist h) = h) ∧
      (∀ x : _root_.BEDC.Derived.BishopDiagonalRegularizationUp,
        bishopDiagonalRegularizationFromEventFlow
            (bishopDiagonalRegularizationToEventFlow x) = some x) ∧
        (∀ x y : _root_.BEDC.Derived.BishopDiagonalRegularizationUp,
          bishopDiagonalRegularizationToEventFlow x =
            bishopDiagonalRegularizationToEventFlow y → x = y) ∧
          bishopDiagonalRegularizationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BishopDiagonalRegularizationTasteGate_single_carrier_alignment_decode,
      ⟨BishopDiagonalRegularizationTasteGate_single_carrier_alignment_round_trip,
        ⟨fun _ _ heq =>
          BishopDiagonalRegularizationTasteGate_single_carrier_alignment_injective heq,
          rfl⟩⟩⟩

end BEDC.Derived.BishopDiagonalRegularizationUp
