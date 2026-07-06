import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NetConvergenceCriterionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NetConvergenceCriterionUp : Type where
  | mk (D N F U T E H C P L : BHist) : NetConvergenceCriterionUp
  deriving DecidableEq

def netConvergenceCriterionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: netConvergenceCriterionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: netConvergenceCriterionEncodeBHist h

def netConvergenceCriterionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (netConvergenceCriterionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (netConvergenceCriterionDecodeBHist tail)

private theorem netConvergenceCriterion_decode_encode_bhist :
    ∀ h : BHist,
      netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def netConvergenceCriterionFields : NetConvergenceCriterionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | NetConvergenceCriterionUp.mk D N F U T E H C P L => [D, N, F, U, T, E, H, C, P, L]

def netConvergenceCriterionToEventFlow : NetConvergenceCriterionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (netConvergenceCriterionFields x).map netConvergenceCriterionEncodeBHist

private def netConvergenceCriterionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => netConvergenceCriterionEventAtDefault index rest

def netConvergenceCriterionFromEventFlow (ef : EventFlow) :
    Option NetConvergenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (NetConvergenceCriterionUp.mk
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 0 ef))
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 1 ef))
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 2 ef))
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 3 ef))
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 4 ef))
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 5 ef))
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 6 ef))
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 7 ef))
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 8 ef))
      (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEventAtDefault 9 ef)))

private theorem netConvergenceCriterion_round_trip (x : NetConvergenceCriterionUp) :
    netConvergenceCriterionFromEventFlow
      (netConvergenceCriterionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D N F U T E H C P L =>
      change
        some
          (NetConvergenceCriterionUp.mk
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist D))
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist N))
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist F))
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist U))
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist T))
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist E))
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist H))
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist C))
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist P))
            (netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist L))) =
          some (NetConvergenceCriterionUp.mk D N F U T E H C P L)
      rw [netConvergenceCriterion_decode_encode_bhist D,
        netConvergenceCriterion_decode_encode_bhist N,
        netConvergenceCriterion_decode_encode_bhist F,
        netConvergenceCriterion_decode_encode_bhist U,
        netConvergenceCriterion_decode_encode_bhist T,
        netConvergenceCriterion_decode_encode_bhist E,
        netConvergenceCriterion_decode_encode_bhist H,
        netConvergenceCriterion_decode_encode_bhist C,
        netConvergenceCriterion_decode_encode_bhist P,
        netConvergenceCriterion_decode_encode_bhist L]

private theorem netConvergenceCriterionToEventFlow_injective
    {x y : NetConvergenceCriterionUp} :
    netConvergenceCriterionToEventFlow x =
      netConvergenceCriterionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      netConvergenceCriterionFromEventFlow (netConvergenceCriterionToEventFlow x) =
        netConvergenceCriterionFromEventFlow (netConvergenceCriterionToEventFlow y) :=
    congrArg netConvergenceCriterionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (netConvergenceCriterion_round_trip x).symm
      (Eq.trans hread (netConvergenceCriterion_round_trip y)))

instance netConvergenceCriterionBHistCarrier :
    BHistCarrier NetConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := netConvergenceCriterionToEventFlow
  fromEventFlow := netConvergenceCriterionFromEventFlow

instance netConvergenceCriterionChapterTasteGate :
    ChapterTasteGate NetConvergenceCriterionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change netConvergenceCriterionFromEventFlow
      (netConvergenceCriterionToEventFlow x) = some x
    exact netConvergenceCriterion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (netConvergenceCriterionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate NetConvergenceCriterionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  netConvergenceCriterionChapterTasteGate

theorem NetConvergenceCriterionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        netConvergenceCriterionDecodeBHist (netConvergenceCriterionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier NetConvergenceCriterionUp) ∧
        Nonempty (ChapterTasteGate NetConvergenceCriterionUp) ∧
          netConvergenceCriterionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨netConvergenceCriterion_decode_encode_bhist,
      ⟨netConvergenceCriterionBHistCarrier⟩,
      ⟨netConvergenceCriterionChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.NetConvergenceCriterionUp
