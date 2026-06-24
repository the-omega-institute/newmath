import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalHalvingUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalHalvingUp : Type where
  | mk (I D M L R W Q E T C P N : BHist) : DyadicIntervalHalvingUp
  deriving DecidableEq

def dyadicIntervalHalvingEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicIntervalHalvingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicIntervalHalvingEncodeBHist h

def dyadicIntervalHalvingDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicIntervalHalvingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicIntervalHalvingDecodeBHist tail)

private theorem DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicIntervalHalvingFields : DyadicIntervalHalvingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalHalvingUp.mk I D M L R W Q E T C P N =>
      [I, D, M, L, R, W, Q, E, T, C, P, N]

def dyadicIntervalHalvingToEventFlow : DyadicIntervalHalvingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (dyadicIntervalHalvingFields x).map dyadicIntervalHalvingEncodeBHist

private def dyadicIntervalHalvingEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicIntervalHalvingEventAtDefault index rest

def dyadicIntervalHalvingFromEventFlow
    (ef : EventFlow) : Option DyadicIntervalHalvingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicIntervalHalvingUp.mk
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 0 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 1 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 2 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 3 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 4 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 5 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 6 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 7 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 8 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 9 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 10 ef))
      (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEventAtDefault 11 ef)))

private theorem DyadicIntervalHalvingTasteGate_single_carrier_alignment_round_trip
    (x : DyadicIntervalHalvingUp) :
    dyadicIntervalHalvingFromEventFlow (dyadicIntervalHalvingToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk I D M L R W Q E T C P N =>
      change
        some
          (DyadicIntervalHalvingUp.mk
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist I))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist D))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist M))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist L))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist R))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist W))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist Q))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist E))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist T))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist C))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist P))
            (dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist N))) =
          some (DyadicIntervalHalvingUp.mk I D M L R W Q E T C P N)
      rw [DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode I,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode D,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode M,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode L,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode R,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode W,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode Q,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode E,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode T,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode C,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode P,
        DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode N]

private theorem DyadicIntervalHalvingTasteGate_single_carrier_alignment_injective
    {x y : DyadicIntervalHalvingUp} :
    dyadicIntervalHalvingToEventFlow x = dyadicIntervalHalvingToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicIntervalHalvingFromEventFlow (dyadicIntervalHalvingToEventFlow x) =
        dyadicIntervalHalvingFromEventFlow (dyadicIntervalHalvingToEventFlow y) :=
    congrArg dyadicIntervalHalvingFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicIntervalHalvingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicIntervalHalvingTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicIntervalHalvingBHistCarrier : BHistCarrier DyadicIntervalHalvingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicIntervalHalvingToEventFlow
  fromEventFlow := dyadicIntervalHalvingFromEventFlow

instance dyadicIntervalHalvingChapterTasteGate :
    ChapterTasteGate DyadicIntervalHalvingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicIntervalHalvingFromEventFlow (dyadicIntervalHalvingToEventFlow x) =
      some x
    exact DyadicIntervalHalvingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicIntervalHalvingTasteGate_single_carrier_alignment_injective heq)

theorem DyadicIntervalHalvingTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicIntervalHalvingDecodeBHist (dyadicIntervalHalvingEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier DyadicIntervalHalvingUp) ∧
        Nonempty (ChapterTasteGate DyadicIntervalHalvingUp) ∧
          dyadicIntervalHalvingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨DyadicIntervalHalvingTasteGate_single_carrier_alignment_decode_encode,
      ⟨dyadicIntervalHalvingBHistCarrier⟩,
      ⟨dyadicIntervalHalvingChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.DyadicIntervalHalvingUp
