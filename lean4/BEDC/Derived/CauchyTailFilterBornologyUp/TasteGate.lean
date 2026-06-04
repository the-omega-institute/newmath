import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailFilterBornologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailFilterBornologyUp : Type where
  | mk (S R B W M E H C P N : BHist) : CauchyTailFilterBornologyUp
  deriving DecidableEq

def cauchyTailFilterBornologyFields : CauchyTailFilterBornologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailFilterBornologyUp.mk S R B W M E H C P N => [S, R, B, W, M, E, H, C, P, N]

def cauchyTailFilterBornologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailFilterBornologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailFilterBornologyEncodeBHist h

def cauchyTailFilterBornologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailFilterBornologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailFilterBornologyDecodeBHist tail)

private theorem cauchyTailFilterBornology_decode_encode_bhist :
    ∀ h : BHist,
      cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyTailFilterBornologyToEventFlow : CauchyTailFilterBornologyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyTailFilterBornologyFields x).map cauchyTailFilterBornologyEncodeBHist

private def cauchyTailFilterBornologyEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyTailFilterBornologyEventAtDefault index rest

def cauchyTailFilterBornologyFromEventFlow
    (ef : EventFlow) : Option CauchyTailFilterBornologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyTailFilterBornologyUp.mk
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 0 ef))
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 1 ef))
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 2 ef))
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 3 ef))
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 4 ef))
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 5 ef))
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 6 ef))
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 7 ef))
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 8 ef))
      (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEventAtDefault 9 ef)))

private theorem cauchyTailFilterBornology_round_trip :
    ∀ x : CauchyTailFilterBornologyUp,
      cauchyTailFilterBornologyFromEventFlow
        (cauchyTailFilterBornologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R B W M E H C P N =>
      change
        some
          (CauchyTailFilterBornologyUp.mk
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist S))
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist R))
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist B))
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist W))
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist M))
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist E))
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist H))
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist C))
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist P))
            (cauchyTailFilterBornologyDecodeBHist (cauchyTailFilterBornologyEncodeBHist N))) =
          some (CauchyTailFilterBornologyUp.mk S R B W M E H C P N)
      rw [cauchyTailFilterBornology_decode_encode_bhist S,
        cauchyTailFilterBornology_decode_encode_bhist R,
        cauchyTailFilterBornology_decode_encode_bhist B,
        cauchyTailFilterBornology_decode_encode_bhist W,
        cauchyTailFilterBornology_decode_encode_bhist M,
        cauchyTailFilterBornology_decode_encode_bhist E,
        cauchyTailFilterBornology_decode_encode_bhist H,
        cauchyTailFilterBornology_decode_encode_bhist C,
        cauchyTailFilterBornology_decode_encode_bhist P,
        cauchyTailFilterBornology_decode_encode_bhist N]

private theorem cauchyTailFilterBornologyToEventFlow_injective
    {x y : CauchyTailFilterBornologyUp} :
    cauchyTailFilterBornologyToEventFlow x = cauchyTailFilterBornologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailFilterBornologyFromEventFlow (cauchyTailFilterBornologyToEventFlow x) =
        cauchyTailFilterBornologyFromEventFlow (cauchyTailFilterBornologyToEventFlow y) :=
    congrArg cauchyTailFilterBornologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyTailFilterBornology_round_trip x).symm
      (Eq.trans hread (cauchyTailFilterBornology_round_trip y)))

instance cauchyTailFilterBornologyBHistCarrier :
    BHistCarrier CauchyTailFilterBornologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailFilterBornologyToEventFlow
  fromEventFlow := cauchyTailFilterBornologyFromEventFlow

instance cauchyTailFilterBornologyChapterTasteGate :
    ChapterTasteGate CauchyTailFilterBornologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyTailFilterBornologyFromEventFlow (cauchyTailFilterBornologyToEventFlow x) = some x
    exact cauchyTailFilterBornology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyTailFilterBornologyToEventFlow_injective heq)

theorem CauchyTailFilterBornologyTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CauchyTailFilterBornologyUp) ∧
      Nonempty (ChapterTasteGate CauchyTailFilterBornologyUp) ∧
        cauchyTailFilterBornologyEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨⟨cauchyTailFilterBornologyBHistCarrier⟩,
    ⟨cauchyTailFilterBornologyChapterTasteGate⟩, rfl⟩

end BEDC.Derived.CauchyTailFilterBornologyUp
