import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealBolzanoWeierstrassUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealBolzanoWeierstrassUp : Type where
  | mk (S D I L R E Q H C P N : BHist) : RealBolzanoWeierstrassUp
  deriving DecidableEq

def realBolzanoWeierstrassEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realBolzanoWeierstrassEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realBolzanoWeierstrassEncodeBHist h

def realBolzanoWeierstrassDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realBolzanoWeierstrassDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realBolzanoWeierstrassDecodeBHist tail)

private theorem realBolzanoWeierstrassDecodeEncode :
    ∀ h : BHist, realBolzanoWeierstrassDecodeBHist
      (realBolzanoWeierstrassEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realBolzanoWeierstrassFields : RealBolzanoWeierstrassUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealBolzanoWeierstrassUp.mk S D I L R E Q H C P N => [S, D, I, L, R, E, Q, H, C, P, N]

def realBolzanoWeierstrassToEventFlow : RealBolzanoWeierstrassUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realBolzanoWeierstrassFields x).map realBolzanoWeierstrassEncodeBHist

private def realBolzanoWeierstrassEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realBolzanoWeierstrassEventAtDefault index rest

def realBolzanoWeierstrassFromEventFlow : EventFlow → Option RealBolzanoWeierstrassUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RealBolzanoWeierstrassUp.mk
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 0 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 1 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 2 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 3 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 4 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 5 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 6 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 7 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 8 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 9 ef))
        (realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEventAtDefault 10 ef)))

private theorem realBolzanoWeierstrassRoundTrip :
    ∀ x : RealBolzanoWeierstrassUp,
      realBolzanoWeierstrassFromEventFlow
        (realBolzanoWeierstrassToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D I L R E Q H C P N =>
      change
        some
          (RealBolzanoWeierstrassUp.mk
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist S))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist D))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist I))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist L))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist R))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist E))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist Q))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist H))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist C))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist P))
            (realBolzanoWeierstrassDecodeBHist
              (realBolzanoWeierstrassEncodeBHist N))) =
          some (RealBolzanoWeierstrassUp.mk S D I L R E Q H C P N)
      rw [realBolzanoWeierstrassDecodeEncode S,
        realBolzanoWeierstrassDecodeEncode D,
        realBolzanoWeierstrassDecodeEncode I,
        realBolzanoWeierstrassDecodeEncode L,
        realBolzanoWeierstrassDecodeEncode R,
        realBolzanoWeierstrassDecodeEncode E,
        realBolzanoWeierstrassDecodeEncode Q,
        realBolzanoWeierstrassDecodeEncode H,
        realBolzanoWeierstrassDecodeEncode C,
        realBolzanoWeierstrassDecodeEncode P,
        realBolzanoWeierstrassDecodeEncode N]

private theorem realBolzanoWeierstrassToEventFlow_injective
    {x y : RealBolzanoWeierstrassUp} :
    realBolzanoWeierstrassToEventFlow x =
      realBolzanoWeierstrassToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realBolzanoWeierstrassFromEventFlow
          (realBolzanoWeierstrassToEventFlow x) =
        realBolzanoWeierstrassFromEventFlow
          (realBolzanoWeierstrassToEventFlow y) :=
    congrArg realBolzanoWeierstrassFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realBolzanoWeierstrassRoundTrip x).symm
      (Eq.trans hread (realBolzanoWeierstrassRoundTrip y)))

instance realBolzanoWeierstrassBHistCarrier :
    BHistCarrier RealBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realBolzanoWeierstrassToEventFlow
  fromEventFlow := realBolzanoWeierstrassFromEventFlow

instance realBolzanoWeierstrassChapterTasteGate :
    ChapterTasteGate RealBolzanoWeierstrassUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realBolzanoWeierstrassFromEventFlow
      (realBolzanoWeierstrassToEventFlow x) = some x
    exact realBolzanoWeierstrassRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realBolzanoWeierstrassToEventFlow_injective heq)

theorem RealBolzanoWeierstrassTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        realBolzanoWeierstrassDecodeBHist (realBolzanoWeierstrassEncodeBHist h) = h) ∧
      (∀ x : RealBolzanoWeierstrassUp,
        realBolzanoWeierstrassFromEventFlow
          (realBolzanoWeierstrassToEventFlow x) = some x) ∧
      Nonempty (BHistCarrier RealBolzanoWeierstrassUp) ∧
        Nonempty (ChapterTasteGate RealBolzanoWeierstrassUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨realBolzanoWeierstrassDecodeEncode,
      realBolzanoWeierstrassRoundTrip,
      ⟨realBolzanoWeierstrassBHistCarrier⟩,
      ⟨realBolzanoWeierstrassChapterTasteGate⟩⟩

end BEDC.Derived.RealBolzanoWeierstrassUp.TasteGate
