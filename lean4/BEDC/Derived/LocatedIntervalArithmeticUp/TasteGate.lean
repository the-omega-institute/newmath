import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalArithmeticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalArithmeticUp : Type where
  | mk (I J D R Q E Add Mul W H C P N : BHist) : LocatedIntervalArithmeticUp
  deriving DecidableEq

def locatedIntervalArithmeticEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalArithmeticEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalArithmeticEncodeBHist h

def locatedIntervalArithmeticDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalArithmeticDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalArithmeticDecodeBHist tail)

private theorem LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedIntervalArithmeticFields : LocatedIntervalArithmeticUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalArithmeticUp.mk I J D R Q E Add Mul W H C P N =>
      [I, J, D, R, Q, E, Add, Mul, W, H, C, P, N]

def locatedIntervalArithmeticToEventFlow : LocatedIntervalArithmeticUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (locatedIntervalArithmeticFields x).map locatedIntervalArithmeticEncodeBHist

private def locatedIntervalArithmeticEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalArithmeticEventAtDefault index rest

def locatedIntervalArithmeticFromEventFlow (ef : EventFlow) : Option LocatedIntervalArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalArithmeticUp.mk
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 0 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 1 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 2 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 3 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 4 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 5 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 6 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 7 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 8 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 9 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 10 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 11 ef))
      (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEventAtDefault 12 ef)))

private theorem LocatedIntervalArithmeticTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedIntervalArithmeticUp,
      locatedIntervalArithmeticFromEventFlow (locatedIntervalArithmeticToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I J D R Q E Add Mul W H C P N =>
      change
        some
          (LocatedIntervalArithmeticUp.mk
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist I))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist J))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist D))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist R))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist Q))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist E))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist Add))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist Mul))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist W))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist H))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist C))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist P))
            (locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist N))) =
          some (LocatedIntervalArithmeticUp.mk I J D R Q E Add Mul W H C P N)
      rw [LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode I,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode J,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode D,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode R,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode Q,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode E,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode Add,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode Mul,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode W,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode H,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode C,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode P,
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode N]

private theorem LocatedIntervalArithmeticTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedIntervalArithmeticUp} :
    locatedIntervalArithmeticToEventFlow x = locatedIntervalArithmeticToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalArithmeticFromEventFlow (locatedIntervalArithmeticToEventFlow x) =
        locatedIntervalArithmeticFromEventFlow (locatedIntervalArithmeticToEventFlow y) :=
    congrArg locatedIntervalArithmeticFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedIntervalArithmeticTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedIntervalArithmeticTasteGate_single_carrier_alignment_round_trip y)))

instance locatedIntervalArithmeticBHistCarrier : BHistCarrier LocatedIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalArithmeticToEventFlow
  fromEventFlow := locatedIntervalArithmeticFromEventFlow

instance locatedIntervalArithmeticChapterTasteGate :
    ChapterTasteGate LocatedIntervalArithmeticUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedIntervalArithmeticFromEventFlow (locatedIntervalArithmeticToEventFlow x) = some x
    exact LocatedIntervalArithmeticTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LocatedIntervalArithmeticTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LocatedIntervalArithmeticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedIntervalArithmeticChapterTasteGate

theorem LocatedIntervalArithmeticTasteGate_single_carrier_alignment :
    (forall h : BHist,
      locatedIntervalArithmeticDecodeBHist (locatedIntervalArithmeticEncodeBHist h) = h) ∧
    (forall x : LocatedIntervalArithmeticUp,
      locatedIntervalArithmeticFromEventFlow (locatedIntervalArithmeticToEventFlow x) = some x) ∧
    (forall x y : LocatedIntervalArithmeticUp,
      locatedIntervalArithmeticToEventFlow x = locatedIntervalArithmeticToEventFlow y -> x = y) ∧
    locatedIntervalArithmeticEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedIntervalArithmeticTasteGate_single_carrier_alignment_decode,
      LocatedIntervalArithmeticTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        LocatedIntervalArithmeticTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.LocatedIntervalArithmeticUp
