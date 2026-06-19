import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealLocallyCompactUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealLocallyCompactUp : Type where
  | mk (R U W D B K A H C P N : BHist) : RealLocallyCompactUp
  deriving DecidableEq

def realLocallyCompactEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realLocallyCompactEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realLocallyCompactEncodeBHist h

def realLocallyCompactDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realLocallyCompactDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realLocallyCompactDecodeBHist tail)

private theorem realLocallyCompact_decode_encode :
    ∀ h : BHist, realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realLocallyCompactFields : RealLocallyCompactUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealLocallyCompactUp.mk R U W D B K A H C P N => [R, U, W, D, B, K, A, H, C, P, N]

def realLocallyCompactToEventFlow : RealLocallyCompactUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realLocallyCompactFields x).map realLocallyCompactEncodeBHist

def realLocallyCompactFromEventFlow : EventFlow → Option RealLocallyCompactUp
  -- BEDC touchpoint anchor: BHist BMark
  | [R, U, W, D, B, K, A, H, C, P, N] =>
      some
        (RealLocallyCompactUp.mk
          (realLocallyCompactDecodeBHist R)
          (realLocallyCompactDecodeBHist U)
          (realLocallyCompactDecodeBHist W)
          (realLocallyCompactDecodeBHist D)
          (realLocallyCompactDecodeBHist B)
          (realLocallyCompactDecodeBHist K)
          (realLocallyCompactDecodeBHist A)
          (realLocallyCompactDecodeBHist H)
          (realLocallyCompactDecodeBHist C)
          (realLocallyCompactDecodeBHist P)
          (realLocallyCompactDecodeBHist N))
  | _ => none

private theorem realLocallyCompact_round_trip (x : RealLocallyCompactUp) :
    realLocallyCompactFromEventFlow (realLocallyCompactToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk R U W D B K A H C P N =>
      change
        some
          (RealLocallyCompactUp.mk
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist R))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist U))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist W))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist D))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist B))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist K))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist A))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist H))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist C))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist P))
            (realLocallyCompactDecodeBHist (realLocallyCompactEncodeBHist N))) =
          some (RealLocallyCompactUp.mk R U W D B K A H C P N)
      rw [realLocallyCompact_decode_encode R, realLocallyCompact_decode_encode U,
        realLocallyCompact_decode_encode W, realLocallyCompact_decode_encode D,
        realLocallyCompact_decode_encode B, realLocallyCompact_decode_encode K,
        realLocallyCompact_decode_encode A, realLocallyCompact_decode_encode H,
        realLocallyCompact_decode_encode C, realLocallyCompact_decode_encode P,
        realLocallyCompact_decode_encode N]

private theorem realLocallyCompactToEventFlow_injective {x y : RealLocallyCompactUp} :
    realLocallyCompactToEventFlow x = realLocallyCompactToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realLocallyCompactFromEventFlow (realLocallyCompactToEventFlow x) =
        realLocallyCompactFromEventFlow (realLocallyCompactToEventFlow y) :=
    congrArg realLocallyCompactFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realLocallyCompact_round_trip x).symm
      (Eq.trans hread (realLocallyCompact_round_trip y)))

instance realLocallyCompactBHistCarrier : BHistCarrier RealLocallyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realLocallyCompactToEventFlow
  fromEventFlow := realLocallyCompactFromEventFlow

instance realLocallyCompactChapterTasteGate : ChapterTasteGate RealLocallyCompactUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realLocallyCompactFromEventFlow (realLocallyCompactToEventFlow x) = some x
    exact realLocallyCompact_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realLocallyCompactToEventFlow_injective heq)

end BEDC.Derived.RealLocallyCompactUp
