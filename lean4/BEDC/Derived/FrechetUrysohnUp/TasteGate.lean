import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FrechetUrysohnUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FrechetUrysohnUp : Type where
  | mk (T S W R A X H C P N : BHist) : FrechetUrysohnUp

def frechetUrysohnEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: frechetUrysohnEncodeBHist h
  | BHist.e1 h => BMark.b1 :: frechetUrysohnEncodeBHist h

def frechetUrysohnDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (frechetUrysohnDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (frechetUrysohnDecodeBHist tail)

private theorem FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def frechetUrysohnFields : FrechetUrysohnUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FrechetUrysohnUp.mk T S W R A X H C P N => [T, S, W, R, A, X, H, C, P, N]

def frechetUrysohnToEventFlow : FrechetUrysohnUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (frechetUrysohnFields x).map frechetUrysohnEncodeBHist

private def frechetUrysohnEventAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => frechetUrysohnEventAt index rest

def frechetUrysohnFromEventFlow (ef : EventFlow) : Option FrechetUrysohnUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FrechetUrysohnUp.mk
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 0 ef))
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 1 ef))
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 2 ef))
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 3 ef))
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 4 ef))
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 5 ef))
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 6 ef))
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 7 ef))
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 8 ef))
      (frechetUrysohnDecodeBHist (frechetUrysohnEventAt 9 ef)))

private theorem FrechetUrysohnTasteGate_single_carrier_alignment_round_trip
    (x : FrechetUrysohnUp) :
    frechetUrysohnFromEventFlow (frechetUrysohnToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T S W R A X H C P N =>
      change
        some
          (FrechetUrysohnUp.mk
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist T))
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist S))
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist W))
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist R))
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist A))
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist X))
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist H))
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist C))
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist P))
            (frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist N))) =
          some (FrechetUrysohnUp.mk T S W R A X H C P N)
      rw [FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode T,
        FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode S,
        FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode W,
        FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode R,
        FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode A,
        FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode X,
        FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode H,
        FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode C,
        FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode P,
        FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode N]

private theorem FrechetUrysohnTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : FrechetUrysohnUp} :
    frechetUrysohnToEventFlow x = frechetUrysohnToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      frechetUrysohnFromEventFlow (frechetUrysohnToEventFlow x) =
        frechetUrysohnFromEventFlow (frechetUrysohnToEventFlow y) :=
    congrArg frechetUrysohnFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FrechetUrysohnTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FrechetUrysohnTasteGate_single_carrier_alignment_round_trip y)))

instance frechetUrysohnBHistCarrier : BHistCarrier FrechetUrysohnUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := frechetUrysohnToEventFlow
  fromEventFlow := frechetUrysohnFromEventFlow

instance frechetUrysohnChapterTasteGate : ChapterTasteGate FrechetUrysohnUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change frechetUrysohnFromEventFlow (frechetUrysohnToEventFlow x) = some x
    exact FrechetUrysohnTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FrechetUrysohnTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem FrechetUrysohnTasteGate_single_carrier_alignment :
    (forall h : BHist, frechetUrysohnDecodeBHist (frechetUrysohnEncodeBHist h) = h) /\
      Nonempty (BHistCarrier FrechetUrysohnUp) /\
        Nonempty (ChapterTasteGate FrechetUrysohnUp) /\
          frechetUrysohnEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨FrechetUrysohnTasteGate_single_carrier_alignment_decode_encode,
      ⟨frechetUrysohnBHistCarrier⟩,
      ⟨frechetUrysohnChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.FrechetUrysohnUp
