import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCantorWindowUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCantorWindowUp : Type where
  | mk (B L D M U R H C P N : BHist) : DyadicCantorWindowUp
  deriving DecidableEq

def dyadicCantorWindowEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCantorWindowEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCantorWindowEncodeBHist h

def dyadicCantorWindowDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCantorWindowDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCantorWindowDecodeBHist tail)

private theorem DyadicCantorWindowTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicCantorWindowDecodeBHist
        (dyadicCantorWindowEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicCantorWindowFields :
    DyadicCantorWindowUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCantorWindowUp.mk B L D M U R H C P N => [B, L, D, M, U, R, H, C, P, N]

def dyadicCantorWindowToEventFlow :
    DyadicCantorWindowUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCantorWindowFields x).map dyadicCantorWindowEncodeBHist

private def dyadicCantorWindowEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      dyadicCantorWindowEventAtDefault index rest

def dyadicCantorWindowFromEventFlow
    (ef : EventFlow) : Option DyadicCantorWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicCantorWindowUp.mk
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 0 ef))
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 1 ef))
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 2 ef))
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 3 ef))
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 4 ef))
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 5 ef))
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 6 ef))
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 7 ef))
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 8 ef))
      (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEventAtDefault 9 ef)))

private theorem DyadicCantorWindowTasteGate_single_carrier_alignment_round_trip
    (x : DyadicCantorWindowUp) :
    dyadicCantorWindowFromEventFlow
      (dyadicCantorWindowToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B L D M U R H C P N =>
      change
        some
          (DyadicCantorWindowUp.mk
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist B))
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist L))
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist D))
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist M))
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist U))
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist R))
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist H))
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist C))
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist P))
            (dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist N))) =
          some (DyadicCantorWindowUp.mk B L D M U R H C P N)
      rw [DyadicCantorWindowTasteGate_single_carrier_alignment_decode B,
        DyadicCantorWindowTasteGate_single_carrier_alignment_decode L,
        DyadicCantorWindowTasteGate_single_carrier_alignment_decode D,
        DyadicCantorWindowTasteGate_single_carrier_alignment_decode M,
        DyadicCantorWindowTasteGate_single_carrier_alignment_decode U,
        DyadicCantorWindowTasteGate_single_carrier_alignment_decode R,
        DyadicCantorWindowTasteGate_single_carrier_alignment_decode H,
        DyadicCantorWindowTasteGate_single_carrier_alignment_decode C,
        DyadicCantorWindowTasteGate_single_carrier_alignment_decode P,
        DyadicCantorWindowTasteGate_single_carrier_alignment_decode N]

private theorem DyadicCantorWindowTasteGate_single_carrier_alignment_injective
    {x y : DyadicCantorWindowUp} :
    dyadicCantorWindowToEventFlow x =
      dyadicCantorWindowToEventFlow y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCantorWindowFromEventFlow
          (dyadicCantorWindowToEventFlow x) =
        dyadicCantorWindowFromEventFlow
          (dyadicCantorWindowToEventFlow y) :=
    congrArg dyadicCantorWindowFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DyadicCantorWindowTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicCantorWindowTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicCantorWindowBHistCarrier :
    BHistCarrier DyadicCantorWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCantorWindowToEventFlow
  fromEventFlow := dyadicCantorWindowFromEventFlow

instance dyadicCantorWindowChapterTasteGate :
    ChapterTasteGate DyadicCantorWindowUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicCantorWindowFromEventFlow
        (dyadicCantorWindowToEventFlow x) = some x
    exact DyadicCantorWindowTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicCantorWindowTasteGate_single_carrier_alignment_injective heq)

def taste_gate : ChapterTasteGate DyadicCantorWindowUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicCantorWindowChapterTasteGate

theorem DyadicCantorWindowTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicCantorWindowDecodeBHist (dyadicCantorWindowEncodeBHist h) = h) ∧
      (∀ x : DyadicCantorWindowUp,
        dyadicCantorWindowFromEventFlow (dyadicCantorWindowToEventFlow x) = some x) ∧
        (∀ x y : DyadicCantorWindowUp,
          dyadicCantorWindowToEventFlow x = dyadicCantorWindowToEventFlow y → x = y) ∧
          dyadicCantorWindowEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DyadicCantorWindowTasteGate_single_carrier_alignment_decode
  · constructor
    · exact DyadicCantorWindowTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact DyadicCantorWindowTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.DyadicCantorWindowUp
