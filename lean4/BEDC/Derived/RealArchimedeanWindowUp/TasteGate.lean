import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealArchimedeanWindowUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealArchimedeanWindowUp : Type where
  | mk (R S Q D L U H C P N : BHist) : RealArchimedeanWindowUp
  deriving DecidableEq

def realArchimedeanWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realArchimedeanWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realArchimedeanWindowEncodeBHist h

def realArchimedeanWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realArchimedeanWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realArchimedeanWindowDecodeBHist tail)

private theorem RealArchimedeanWindowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realArchimedeanWindowDecodeBHist
      (realArchimedeanWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realArchimedeanWindowFields : RealArchimedeanWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealArchimedeanWindowUp.mk R S Q D L U H C P N => [R, S, Q, D, L, U, H, C, P, N]

def realArchimedeanWindowToEventFlow : RealArchimedeanWindowUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (realArchimedeanWindowFields x).map realArchimedeanWindowEncodeBHist

private def realArchimedeanWindowEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realArchimedeanWindowEventAtDefault index rest

def realArchimedeanWindowFromEventFlow
    (ef : EventFlow) : Option RealArchimedeanWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealArchimedeanWindowUp.mk
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 0 ef))
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 1 ef))
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 2 ef))
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 3 ef))
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 4 ef))
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 5 ef))
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 6 ef))
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 7 ef))
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 8 ef))
      (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEventAtDefault 9 ef)))

private theorem RealArchimedeanWindowTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealArchimedeanWindowUp,
      realArchimedeanWindowFromEventFlow (realArchimedeanWindowToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S Q D L U H C P N =>
      change
        some
          (RealArchimedeanWindowUp.mk
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist R))
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist S))
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist Q))
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist D))
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist L))
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist U))
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist H))
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist C))
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist P))
            (realArchimedeanWindowDecodeBHist (realArchimedeanWindowEncodeBHist N))) =
          some (RealArchimedeanWindowUp.mk R S Q D L U H C P N)
      rw [RealArchimedeanWindowTasteGate_single_carrier_alignment_decode R,
        RealArchimedeanWindowTasteGate_single_carrier_alignment_decode S,
        RealArchimedeanWindowTasteGate_single_carrier_alignment_decode Q,
        RealArchimedeanWindowTasteGate_single_carrier_alignment_decode D,
        RealArchimedeanWindowTasteGate_single_carrier_alignment_decode L,
        RealArchimedeanWindowTasteGate_single_carrier_alignment_decode U,
        RealArchimedeanWindowTasteGate_single_carrier_alignment_decode H,
        RealArchimedeanWindowTasteGate_single_carrier_alignment_decode C,
        RealArchimedeanWindowTasteGate_single_carrier_alignment_decode P,
        RealArchimedeanWindowTasteGate_single_carrier_alignment_decode N]

private theorem RealArchimedeanWindowTasteGate_single_carrier_alignment_injective
    {x y : RealArchimedeanWindowUp} :
    realArchimedeanWindowToEventFlow x = realArchimedeanWindowToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realArchimedeanWindowFromEventFlow (realArchimedeanWindowToEventFlow x) =
        realArchimedeanWindowFromEventFlow (realArchimedeanWindowToEventFlow y) :=
    congrArg realArchimedeanWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealArchimedeanWindowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealArchimedeanWindowTasteGate_single_carrier_alignment_round_trip y)))

instance realArchimedeanWindowBHistCarrier : BHistCarrier RealArchimedeanWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realArchimedeanWindowToEventFlow
  fromEventFlow := realArchimedeanWindowFromEventFlow

instance realArchimedeanWindowChapterTasteGate :
    ChapterTasteGate RealArchimedeanWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realArchimedeanWindowFromEventFlow (realArchimedeanWindowToEventFlow x) = some x
    exact RealArchimedeanWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealArchimedeanWindowTasteGate_single_carrier_alignment_injective heq)

theorem RealArchimedeanWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist, realArchimedeanWindowDecodeBHist
      (realArchimedeanWindowEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier RealArchimedeanWindowUp) ∧
        Nonempty (ChapterTasteGate RealArchimedeanWindowUp) ∧
          realArchimedeanWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RealArchimedeanWindowTasteGate_single_carrier_alignment_decode,
      ⟨realArchimedeanWindowBHistCarrier⟩,
      ⟨realArchimedeanWindowChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.RealArchimedeanWindowUp.TasteGate
