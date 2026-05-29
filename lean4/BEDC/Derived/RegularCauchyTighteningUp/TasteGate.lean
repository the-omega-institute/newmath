import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTighteningUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTighteningUp : Type where
  | mk (D S R F T H C P N : BHist) : RegularCauchyTighteningUp
  deriving DecidableEq

def regularCauchyTighteningEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTighteningEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTighteningEncodeBHist h

def regularCauchyTighteningDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTighteningDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTighteningDecodeBHist tail)

private theorem regularCauchyTightening_decode_encode :
    forall h : BHist,
      regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTighteningFields : RegularCauchyTighteningUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTighteningUp.mk D S R F T H C P N => [D, S, R, F, T, H, C, P, N]

def regularCauchyTighteningToEventFlow : RegularCauchyTighteningUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (regularCauchyTighteningFields token).map regularCauchyTighteningEncodeBHist

private def regularCauchyTighteningEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTighteningEventAtDefault index rest

def regularCauchyTighteningFromEventFlow
    (ef : EventFlow) : Option RegularCauchyTighteningUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTighteningUp.mk
      (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEventAtDefault 0 ef))
      (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEventAtDefault 1 ef))
      (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEventAtDefault 2 ef))
      (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEventAtDefault 3 ef))
      (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEventAtDefault 4 ef))
      (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEventAtDefault 5 ef))
      (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEventAtDefault 6 ef))
      (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEventAtDefault 7 ef))
      (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEventAtDefault 8 ef)))

private theorem regularCauchyTightening_round_trip :
    forall x : RegularCauchyTighteningUp,
      regularCauchyTighteningFromEventFlow (regularCauchyTighteningToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R F T H C P N =>
      change
        some
          (RegularCauchyTighteningUp.mk
            (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist D))
            (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist S))
            (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist R))
            (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist F))
            (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist T))
            (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist H))
            (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist C))
            (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist P))
            (regularCauchyTighteningDecodeBHist (regularCauchyTighteningEncodeBHist N))) =
          some (RegularCauchyTighteningUp.mk D S R F T H C P N)
      rw [regularCauchyTightening_decode_encode D,
        regularCauchyTightening_decode_encode S,
        regularCauchyTightening_decode_encode R,
        regularCauchyTightening_decode_encode F,
        regularCauchyTightening_decode_encode T,
        regularCauchyTightening_decode_encode H,
        regularCauchyTightening_decode_encode C,
        regularCauchyTightening_decode_encode P,
        regularCauchyTightening_decode_encode N]

private theorem regularCauchyTighteningToEventFlow_injective
    {x y : RegularCauchyTighteningUp} :
    regularCauchyTighteningToEventFlow x = regularCauchyTighteningToEventFlow y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTighteningFromEventFlow (regularCauchyTighteningToEventFlow x) =
        regularCauchyTighteningFromEventFlow (regularCauchyTighteningToEventFlow y) :=
    congrArg regularCauchyTighteningFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyTightening_round_trip x).symm
      (Eq.trans hread (regularCauchyTightening_round_trip y)))

instance regularCauchyTighteningBHistCarrier : BHistCarrier RegularCauchyTighteningUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTighteningToEventFlow
  fromEventFlow := regularCauchyTighteningFromEventFlow

instance regularCauchyTighteningChapterTasteGate :
    ChapterTasteGate RegularCauchyTighteningUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTighteningFromEventFlow (regularCauchyTighteningToEventFlow x) =
        some x
    exact regularCauchyTightening_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyTighteningToEventFlow_injective heq)

theorem RegularCauchyTighteningTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RegularCauchyTighteningUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyTighteningUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨⟨regularCauchyTighteningBHistCarrier⟩, ⟨regularCauchyTighteningChapterTasteGate⟩⟩

end BEDC.Derived.RegularCauchyTighteningUp
