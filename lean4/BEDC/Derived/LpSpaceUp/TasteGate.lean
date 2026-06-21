import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LpSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LpSpaceUp : Type where
  | mk (M R V N B I E H C Q A : BHist) : LpSpaceUp
  deriving DecidableEq

def lpSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lpSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lpSpaceEncodeBHist h

def lpSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lpSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lpSpaceDecodeBHist tail)

private theorem LpSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, lpSpaceDecodeBHist (lpSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lpSpaceFields : LpSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LpSpaceUp.mk M R V N B I E H C Q A => [M, R, V, N, B, I, E, H, C, Q, A]

def lpSpaceToEventFlow : LpSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lpSpaceFields x).map lpSpaceEncodeBHist

private def lpSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lpSpaceEventAtDefault index rest

def lpSpaceFromEventFlow : EventFlow → Option LpSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (LpSpaceUp.mk
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 0 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 1 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 2 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 3 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 4 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 5 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 6 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 7 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 8 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 9 ef))
        (lpSpaceDecodeBHist (lpSpaceEventAtDefault 10 ef)))

private theorem LpSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LpSpaceUp, lpSpaceFromEventFlow (lpSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M R V N B I E H C Q A =>
      change
        some
          (LpSpaceUp.mk
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist M))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist R))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist V))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist N))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist B))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist I))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist E))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist H))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist C))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist Q))
            (lpSpaceDecodeBHist (lpSpaceEncodeBHist A))) =
          some (LpSpaceUp.mk M R V N B I E H C Q A)
      rw [LpSpaceTasteGate_single_carrier_alignment_decode M,
        LpSpaceTasteGate_single_carrier_alignment_decode R,
        LpSpaceTasteGate_single_carrier_alignment_decode V,
        LpSpaceTasteGate_single_carrier_alignment_decode N,
        LpSpaceTasteGate_single_carrier_alignment_decode B,
        LpSpaceTasteGate_single_carrier_alignment_decode I,
        LpSpaceTasteGate_single_carrier_alignment_decode E,
        LpSpaceTasteGate_single_carrier_alignment_decode H,
        LpSpaceTasteGate_single_carrier_alignment_decode C,
        LpSpaceTasteGate_single_carrier_alignment_decode Q,
        LpSpaceTasteGate_single_carrier_alignment_decode A]

private theorem LpSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LpSpaceUp} :
    lpSpaceToEventFlow x = lpSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lpSpaceFromEventFlow (lpSpaceToEventFlow x) =
        lpSpaceFromEventFlow (lpSpaceToEventFlow y) :=
    congrArg lpSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LpSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LpSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance lpSpaceBHistCarrier : BHistCarrier LpSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lpSpaceToEventFlow
  fromEventFlow := lpSpaceFromEventFlow

instance lpSpaceChapterTasteGate : ChapterTasteGate LpSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lpSpaceFromEventFlow (lpSpaceToEventFlow x) = some x
    exact LpSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LpSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate LpSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lpSpaceChapterTasteGate

theorem LpSpaceTasteGate_single_carrier_alignment :
    (∃ x : LpSpaceUp,
        lpSpaceFields x =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty]) ∧
      Nonempty (BHistCarrier LpSpaceUp) ∧ Nonempty (ChapterTasteGate LpSpaceUp) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  exact
    ⟨⟨LpSpaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, rfl⟩,
      ⟨lpSpaceBHistCarrier⟩, ⟨lpSpaceChapterTasteGate⟩⟩

end BEDC.Derived.LpSpaceUp
