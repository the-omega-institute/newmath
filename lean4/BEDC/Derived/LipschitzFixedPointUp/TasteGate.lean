import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LipschitzFixedPointUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LipschitzFixedPointUp : Type where
  | mk (B M O R E H C P N : BHist) : LipschitzFixedPointUp
  deriving DecidableEq

def lipschitzFixedPointEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lipschitzFixedPointEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lipschitzFixedPointEncodeBHist h

def lipschitzFixedPointDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lipschitzFixedPointDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lipschitzFixedPointDecodeBHist tail)

private theorem lipschitzFixedPointDecodeEncode :
    forall h : BHist,
      lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lipschitzFixedPointFields : LipschitzFixedPointUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LipschitzFixedPointUp.mk B M O R E H C P N => [B, M, O, R, E, H, C, P, N]

def lipschitzFixedPointToEventFlow : LipschitzFixedPointUp -> EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (lipschitzFixedPointFields x).map lipschitzFixedPointEncodeBHist

private def lipschitzFixedPointEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lipschitzFixedPointEventAtDefault index rest

def lipschitzFixedPointFromEventFlow (ef : EventFlow) : Option LipschitzFixedPointUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LipschitzFixedPointUp.mk
      (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEventAtDefault 0 ef))
      (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEventAtDefault 1 ef))
      (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEventAtDefault 2 ef))
      (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEventAtDefault 3 ef))
      (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEventAtDefault 4 ef))
      (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEventAtDefault 5 ef))
      (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEventAtDefault 6 ef))
      (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEventAtDefault 7 ef))
      (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEventAtDefault 8 ef)))

private theorem lipschitzFixedPointRoundTrip :
    forall x : LipschitzFixedPointUp,
      lipschitzFixedPointFromEventFlow (lipschitzFixedPointToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B M O R E H C P N =>
      change
        some
          (LipschitzFixedPointUp.mk
            (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist B))
            (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist M))
            (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist O))
            (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist R))
            (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist E))
            (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist H))
            (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist C))
            (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist P))
            (lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist N))) =
          some (LipschitzFixedPointUp.mk B M O R E H C P N)
      rw [lipschitzFixedPointDecodeEncode B, lipschitzFixedPointDecodeEncode M,
        lipschitzFixedPointDecodeEncode O, lipschitzFixedPointDecodeEncode R,
        lipschitzFixedPointDecodeEncode E, lipschitzFixedPointDecodeEncode H,
        lipschitzFixedPointDecodeEncode C, lipschitzFixedPointDecodeEncode P,
        lipschitzFixedPointDecodeEncode N]

private theorem lipschitzFixedPointToEventFlow_injective
    {x y : LipschitzFixedPointUp} :
    lipschitzFixedPointToEventFlow x = lipschitzFixedPointToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lipschitzFixedPointFromEventFlow (lipschitzFixedPointToEventFlow x) =
        lipschitzFixedPointFromEventFlow (lipschitzFixedPointToEventFlow y) :=
    congrArg lipschitzFixedPointFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lipschitzFixedPointRoundTrip x).symm
      (Eq.trans hread (lipschitzFixedPointRoundTrip y)))

instance lipschitzFixedPointBHistCarrier : BHistCarrier LipschitzFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lipschitzFixedPointToEventFlow
  fromEventFlow := lipschitzFixedPointFromEventFlow

instance lipschitzFixedPointChapterTasteGate : ChapterTasteGate LipschitzFixedPointUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lipschitzFixedPointFromEventFlow (lipschitzFixedPointToEventFlow x) = some x
    exact lipschitzFixedPointRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lipschitzFixedPointToEventFlow_injective heq)

theorem LipschitzFixedPointTasteGate_single_carrier_alignment :
    (forall h : BHist, lipschitzFixedPointDecodeBHist (lipschitzFixedPointEncodeBHist h) = h) ∧
      (forall x : LipschitzFixedPointUp,
        lipschitzFixedPointFromEventFlow (lipschitzFixedPointToEventFlow x) = some x) ∧
        (forall x y : LipschitzFixedPointUp,
          lipschitzFixedPointToEventFlow x = lipschitzFixedPointToEventFlow y -> x = y) ∧
          lipschitzFixedPointEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨lipschitzFixedPointDecodeEncode,
      lipschitzFixedPointRoundTrip,
      (fun _x _y heq => lipschitzFixedPointToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LipschitzFixedPointUp.TasteGate
