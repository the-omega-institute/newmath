import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoincareVisualRadiusLadderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoincareVisualRadiusLadderUp : Type where
  | mk (D R B V O S Q E T A H C P N : BHist) : PoincareVisualRadiusLadderUp
  deriving DecidableEq

def poincareVisualRadiusLadderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poincareVisualRadiusLadderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poincareVisualRadiusLadderEncodeBHist h

def poincareVisualRadiusLadderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poincareVisualRadiusLadderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poincareVisualRadiusLadderDecodeBHist tail)

private theorem PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def poincareVisualRadiusLadderFields : PoincareVisualRadiusLadderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoincareVisualRadiusLadderUp.mk D R B V O S Q E T A H C P N =>
      [D, R, B, V, O, S, Q, E, T, A, H, C, P, N]

def poincareVisualRadiusLadderToEventFlow : PoincareVisualRadiusLadderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (poincareVisualRadiusLadderFields x).map poincareVisualRadiusLadderEncodeBHist

private def poincareVisualRadiusLadderEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => poincareVisualRadiusLadderEventAtDefault index rest

def poincareVisualRadiusLadderFromEventFlow
    (ef : EventFlow) : Option PoincareVisualRadiusLadderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (PoincareVisualRadiusLadderUp.mk
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 0 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 1 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 2 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 3 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 4 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 5 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 6 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 7 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 8 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 9 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 10 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 11 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 12 ef))
      (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEventAtDefault 13 ef)))

private theorem PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_round_trip
    (x : PoincareVisualRadiusLadderUp) :
    poincareVisualRadiusLadderFromEventFlow (poincareVisualRadiusLadderToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk D R B V O S Q E T A H C P N =>
      change
        some
          (PoincareVisualRadiusLadderUp.mk
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist D))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist R))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist B))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist V))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist O))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist S))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist Q))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist E))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist T))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist A))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist H))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist C))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist P))
            (poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist N))) =
          some (PoincareVisualRadiusLadderUp.mk D R B V O S Q E T A H C P N)
      rw [PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode D,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode R,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode B,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode V,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode O,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode S,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode Q,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode E,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode T,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode A,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode H,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode C,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode P,
        PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode N]

private theorem PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : PoincareVisualRadiusLadderUp} :
    poincareVisualRadiusLadderToEventFlow x = poincareVisualRadiusLadderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poincareVisualRadiusLadderFromEventFlow (poincareVisualRadiusLadderToEventFlow x) =
        poincareVisualRadiusLadderFromEventFlow (poincareVisualRadiusLadderToEventFlow y) :=
    congrArg poincareVisualRadiusLadderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_round_trip y)))

instance poincareVisualRadiusLadderBHistCarrier : BHistCarrier PoincareVisualRadiusLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poincareVisualRadiusLadderToEventFlow
  fromEventFlow := poincareVisualRadiusLadderFromEventFlow

instance poincareVisualRadiusLadderChapterTasteGate :
    ChapterTasteGate PoincareVisualRadiusLadderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      poincareVisualRadiusLadderFromEventFlow (poincareVisualRadiusLadderToEventFlow x) =
        some x
    exact PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate PoincareVisualRadiusLadderUp :=
  -- BEDC touchpoint anchor: BHist BMark
  poincareVisualRadiusLadderChapterTasteGate

theorem PoincareVisualRadiusLadderTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        poincareVisualRadiusLadderDecodeBHist (poincareVisualRadiusLadderEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier PoincareVisualRadiusLadderUp) ∧
        Nonempty (ChapterTasteGate PoincareVisualRadiusLadderUp) ∧
          poincareVisualRadiusLadderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨PoincareVisualRadiusLadderTasteGate_single_carrier_alignment_decode,
      ⟨poincareVisualRadiusLadderBHistCarrier⟩,
      ⟨poincareVisualRadiusLadderChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.PoincareVisualRadiusLadderUp
