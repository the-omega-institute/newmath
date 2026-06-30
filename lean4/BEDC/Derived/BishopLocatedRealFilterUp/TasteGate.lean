import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BishopLocatedRealFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BishopLocatedRealFilterUp : Type where
  | mk (F L D W R E B H T P N : BHist) : BishopLocatedRealFilterUp
  deriving DecidableEq

def bishopLocatedRealFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bishopLocatedRealFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bishopLocatedRealFilterEncodeBHist h

def bishopLocatedRealFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bishopLocatedRealFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bishopLocatedRealFilterDecodeBHist tail)

private theorem bishopLocatedRealFilter_decode_encode :
    ∀ h : BHist,
      bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def bishopLocatedRealFilterFields : BishopLocatedRealFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BishopLocatedRealFilterUp.mk F L D W R E B H T P N => [F, L, D, W, R, E, B, H, T, P, N]

def bishopLocatedRealFilterToEventFlow : BishopLocatedRealFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bishopLocatedRealFilterFields x).map bishopLocatedRealFilterEncodeBHist

def bishopLocatedRealFilterFromEventFlow : EventFlow → Option BishopLocatedRealFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [F, L, D, W, R, E, B, H, T, P, N] =>
      some
        (BishopLocatedRealFilterUp.mk
          (bishopLocatedRealFilterDecodeBHist F)
          (bishopLocatedRealFilterDecodeBHist L)
          (bishopLocatedRealFilterDecodeBHist D)
          (bishopLocatedRealFilterDecodeBHist W)
          (bishopLocatedRealFilterDecodeBHist R)
          (bishopLocatedRealFilterDecodeBHist E)
          (bishopLocatedRealFilterDecodeBHist B)
          (bishopLocatedRealFilterDecodeBHist H)
          (bishopLocatedRealFilterDecodeBHist T)
          (bishopLocatedRealFilterDecodeBHist P)
          (bishopLocatedRealFilterDecodeBHist N))
  | _ => none

private theorem bishopLocatedRealFilter_round_trip (x : BishopLocatedRealFilterUp) :
    bishopLocatedRealFilterFromEventFlow (bishopLocatedRealFilterToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F L D W R E B H T P N =>
      change
        some
          (BishopLocatedRealFilterUp.mk
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist F))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist L))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist D))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist W))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist R))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist E))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist B))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist H))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist T))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist P))
            (bishopLocatedRealFilterDecodeBHist (bishopLocatedRealFilterEncodeBHist N))) =
          some (BishopLocatedRealFilterUp.mk F L D W R E B H T P N)
      rw [bishopLocatedRealFilter_decode_encode F, bishopLocatedRealFilter_decode_encode L,
        bishopLocatedRealFilter_decode_encode D, bishopLocatedRealFilter_decode_encode W,
        bishopLocatedRealFilter_decode_encode R, bishopLocatedRealFilter_decode_encode E,
        bishopLocatedRealFilter_decode_encode B, bishopLocatedRealFilter_decode_encode H,
        bishopLocatedRealFilter_decode_encode T, bishopLocatedRealFilter_decode_encode P,
        bishopLocatedRealFilter_decode_encode N]

private theorem bishopLocatedRealFilterToEventFlow_injective
    {x y : BishopLocatedRealFilterUp} :
    bishopLocatedRealFilterToEventFlow x = bishopLocatedRealFilterToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bishopLocatedRealFilterFromEventFlow (bishopLocatedRealFilterToEventFlow x) =
        bishopLocatedRealFilterFromEventFlow (bishopLocatedRealFilterToEventFlow y) :=
    congrArg bishopLocatedRealFilterFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bishopLocatedRealFilter_round_trip x).symm
      (Eq.trans hread (bishopLocatedRealFilter_round_trip y)))

instance bishopLocatedRealFilterBHistCarrier :
    BHistCarrier BishopLocatedRealFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bishopLocatedRealFilterToEventFlow
  fromEventFlow := bishopLocatedRealFilterFromEventFlow

instance bishopLocatedRealFilterChapterTasteGate :
    ChapterTasteGate BishopLocatedRealFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bishopLocatedRealFilterFromEventFlow (bishopLocatedRealFilterToEventFlow x) = some x
    exact bishopLocatedRealFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bishopLocatedRealFilterToEventFlow_injective heq)

end BEDC.Derived.BishopLocatedRealFilterUp
