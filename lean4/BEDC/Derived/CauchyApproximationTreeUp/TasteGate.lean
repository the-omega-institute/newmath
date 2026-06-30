import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyApproximationTreeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyApproximationTreeUp : Type where
  | mk (V E B D S R L H C P N : BHist) : CauchyApproximationTreeUp
  deriving DecidableEq

def cauchyApproximationTreeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyApproximationTreeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyApproximationTreeEncodeBHist h

def cauchyApproximationTreeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyApproximationTreeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyApproximationTreeDecodeBHist tail)

private theorem cauchyApproximationTree_decode_encode_bhist :
    ∀ h : BHist,
      cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def cauchyApproximationTreeFields : CauchyApproximationTreeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyApproximationTreeUp.mk V E B D S R L H C P N =>
      [V, E, B, D, S, R, L, H, C, P, N]

def cauchyApproximationTreeToEventFlow : CauchyApproximationTreeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyApproximationTreeFields x).map cauchyApproximationTreeEncodeBHist

private def cauchyApproximationTreeEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyApproximationTreeEventAtDefault index rest

def cauchyApproximationTreeFromEventFlow
    (ef : EventFlow) : Option CauchyApproximationTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyApproximationTreeUp.mk
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 0 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 1 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 2 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 3 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 4 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 5 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 6 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 7 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 8 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 9 ef))
      (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEventAtDefault 10 ef)))

private theorem cauchyApproximationTree_round_trip :
    ∀ x : CauchyApproximationTreeUp,
      cauchyApproximationTreeFromEventFlow (cauchyApproximationTreeToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk V E B D S R L H C P N =>
      change
        some
          (CauchyApproximationTreeUp.mk
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist V))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist E))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist B))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist D))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist S))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist R))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist L))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist H))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist C))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist P))
            (cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist N))) =
          some (CauchyApproximationTreeUp.mk V E B D S R L H C P N)
      rw [cauchyApproximationTree_decode_encode_bhist V,
        cauchyApproximationTree_decode_encode_bhist E,
        cauchyApproximationTree_decode_encode_bhist B,
        cauchyApproximationTree_decode_encode_bhist D,
        cauchyApproximationTree_decode_encode_bhist S,
        cauchyApproximationTree_decode_encode_bhist R,
        cauchyApproximationTree_decode_encode_bhist L,
        cauchyApproximationTree_decode_encode_bhist H,
        cauchyApproximationTree_decode_encode_bhist C,
        cauchyApproximationTree_decode_encode_bhist P,
        cauchyApproximationTree_decode_encode_bhist N]

private theorem cauchyApproximationTreeToEventFlow_injective
    {x y : CauchyApproximationTreeUp} :
    cauchyApproximationTreeToEventFlow x = cauchyApproximationTreeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyApproximationTreeFromEventFlow (cauchyApproximationTreeToEventFlow x) =
        cauchyApproximationTreeFromEventFlow (cauchyApproximationTreeToEventFlow y) :=
    congrArg cauchyApproximationTreeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyApproximationTree_round_trip x).symm
      (Eq.trans hread (cauchyApproximationTree_round_trip y)))

instance cauchyApproximationTreeBHistCarrier :
    BHistCarrier CauchyApproximationTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyApproximationTreeToEventFlow
  fromEventFlow := cauchyApproximationTreeFromEventFlow

instance cauchyApproximationTreeChapterTasteGate :
    ChapterTasteGate CauchyApproximationTreeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyApproximationTreeFromEventFlow (cauchyApproximationTreeToEventFlow x) =
      some x
    exact cauchyApproximationTree_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyApproximationTreeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyApproximationTreeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyApproximationTreeChapterTasteGate

theorem CauchyApproximationTreeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyApproximationTreeDecodeBHist (cauchyApproximationTreeEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyApproximationTreeUp) ∧
        Nonempty (ChapterTasteGate CauchyApproximationTreeUp) ∧
          cauchyApproximationTreeEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨cauchyApproximationTree_decode_encode_bhist,
      ⟨cauchyApproximationTreeBHistCarrier⟩,
      ⟨cauchyApproximationTreeChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyApproximationTreeUp
