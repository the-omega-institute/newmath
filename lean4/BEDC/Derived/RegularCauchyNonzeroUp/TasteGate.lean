import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyNonzeroUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyNonzeroUp : Type where
  | mk (Q A W D R E H C P N : BHist) : RegularCauchyNonzeroUp
  deriving DecidableEq

def regularCauchyNonzeroEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyNonzeroEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyNonzeroEncodeBHist h

def regularCauchyNonzeroDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyNonzeroDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyNonzeroDecodeBHist tail)

private theorem RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyNonzeroFields : RegularCauchyNonzeroUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyNonzeroUp.mk Q A W D R E H C P N => [Q, A, W, D, R, E, H, C, P, N]

def regularCauchyNonzeroToEventFlow : RegularCauchyNonzeroUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyNonzeroFields x).map regularCauchyNonzeroEncodeBHist

private def regularCauchyNonzeroEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyNonzeroEventAtDefault index rest

def regularCauchyNonzeroFromEventFlow : EventFlow → Option RegularCauchyNonzeroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (RegularCauchyNonzeroUp.mk
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 0 flow))
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 1 flow))
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 2 flow))
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 3 flow))
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 4 flow))
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 5 flow))
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 6 flow))
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 7 flow))
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 8 flow))
        (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEventAtDefault 9 flow)))

private theorem RegularCauchyNonzeroTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyNonzeroUp,
      regularCauchyNonzeroFromEventFlow (regularCauchyNonzeroToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q A W D R E H C P N =>
      change
        some
          (RegularCauchyNonzeroUp.mk
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist Q))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist A))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist W))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist D))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist R))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist E))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist H))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist C))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist P))
            (regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist N))) =
          some (RegularCauchyNonzeroUp.mk Q A W D R E H C P N)
      rw [RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode A,
        RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyNonzeroTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyNonzeroUp} :
    regularCauchyNonzeroToEventFlow x = regularCauchyNonzeroToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyNonzeroFromEventFlow (regularCauchyNonzeroToEventFlow x) =
        regularCauchyNonzeroFromEventFlow (regularCauchyNonzeroToEventFlow y) :=
    congrArg regularCauchyNonzeroFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyNonzeroTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyNonzeroTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyNonzeroBHistCarrier : BHistCarrier RegularCauchyNonzeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyNonzeroToEventFlow
  fromEventFlow := regularCauchyNonzeroFromEventFlow

instance regularCauchyNonzeroChapterTasteGate :
    ChapterTasteGate RegularCauchyNonzeroUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change regularCauchyNonzeroFromEventFlow (regularCauchyNonzeroToEventFlow x) = some x
    exact RegularCauchyNonzeroTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyNonzeroTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate RegularCauchyNonzeroUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyNonzeroChapterTasteGate

theorem RegularCauchyNonzeroTasteGate_single_carrier_alignment :
    (∀ h : BHist, regularCauchyNonzeroDecodeBHist (regularCauchyNonzeroEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RegularCauchyNonzeroUp) ∧
        Nonempty (ChapterTasteGate RegularCauchyNonzeroUp) ∧
          regularCauchyNonzeroEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyNonzeroTasteGate_single_carrier_alignment_decode_encode,
      ⟨regularCauchyNonzeroBHistCarrier⟩,
      ⟨regularCauchyNonzeroChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RegularCauchyNonzeroUp
