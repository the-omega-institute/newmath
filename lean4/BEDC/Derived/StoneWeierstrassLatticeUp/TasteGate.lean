import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StoneWeierstrassLatticeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StoneWeierstrassLatticeUp : Type where
  | mk (K F A S B R H C P N : BHist) : StoneWeierstrassLatticeUp
  deriving DecidableEq

def stoneWeierstrassLatticeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: stoneWeierstrassLatticeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: stoneWeierstrassLatticeEncodeBHist h

def stoneWeierstrassLatticeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (stoneWeierstrassLatticeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (stoneWeierstrassLatticeDecodeBHist tail)

private theorem StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def stoneWeierstrassLatticeFields : StoneWeierstrassLatticeUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | StoneWeierstrassLatticeUp.mk K F A S B R H C P N => [K, F, A, S, B, R, H, C, P, N]

def stoneWeierstrassLatticeToEventFlow : StoneWeierstrassLatticeUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map stoneWeierstrassLatticeEncodeBHist (stoneWeierstrassLatticeFields x)

private def stoneWeierstrassLatticeRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => stoneWeierstrassLatticeRawAt index rest

def stoneWeierstrassLatticeFromEventFlow (flow : EventFlow) :
    Option StoneWeierstrassLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (StoneWeierstrassLatticeUp.mk
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 0 flow))
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 1 flow))
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 2 flow))
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 3 flow))
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 4 flow))
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 5 flow))
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 6 flow))
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 7 flow))
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 8 flow))
      (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeRawAt 9 flow)))

private theorem StoneWeierstrassLatticeTasteGate_single_carrier_alignment_round_trip :
    ∀ x : StoneWeierstrassLatticeUp,
      stoneWeierstrassLatticeFromEventFlow
        (stoneWeierstrassLatticeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K F A S B R H C P N =>
      change
        some
          (StoneWeierstrassLatticeUp.mk
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist K))
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist F))
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist A))
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist S))
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist B))
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist R))
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist H))
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist C))
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist P))
            (stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist N))) =
          some (StoneWeierstrassLatticeUp.mk K F A S B R H C P N)
      rw [StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode K,
        StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode F,
        StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode A,
        StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode S,
        StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode B,
        StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode R,
        StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode H,
        StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode C,
        StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode P,
        StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode N]

private theorem StoneWeierstrassLatticeToEventFlow_injective
    {x y : StoneWeierstrassLatticeUp} :
    stoneWeierstrassLatticeToEventFlow x = stoneWeierstrassLatticeToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      stoneWeierstrassLatticeFromEventFlow (stoneWeierstrassLatticeToEventFlow x) =
        stoneWeierstrassLatticeFromEventFlow (stoneWeierstrassLatticeToEventFlow y) :=
    congrArg stoneWeierstrassLatticeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (StoneWeierstrassLatticeTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (StoneWeierstrassLatticeTasteGate_single_carrier_alignment_round_trip y)))

instance stoneWeierstrassLatticeBHistCarrier :
    BHistCarrier StoneWeierstrassLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := stoneWeierstrassLatticeToEventFlow
  fromEventFlow := stoneWeierstrassLatticeFromEventFlow

instance stoneWeierstrassLatticeChapterTasteGate :
    ChapterTasteGate StoneWeierstrassLatticeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      stoneWeierstrassLatticeFromEventFlow (stoneWeierstrassLatticeToEventFlow x) =
        some x
    exact StoneWeierstrassLatticeTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (StoneWeierstrassLatticeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate StoneWeierstrassLatticeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  stoneWeierstrassLatticeChapterTasteGate

theorem StoneWeierstrassLatticeTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      stoneWeierstrassLatticeDecodeBHist (stoneWeierstrassLatticeEncodeBHist h) = h) ∧
      (∀ x : StoneWeierstrassLatticeUp,
        stoneWeierstrassLatticeFromEventFlow
          (stoneWeierstrassLatticeToEventFlow x) = some x) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨StoneWeierstrassLatticeTasteGate_single_carrier_alignment_decode,
      StoneWeierstrassLatticeTasteGate_single_carrier_alignment_round_trip⟩

end BEDC.Derived.StoneWeierstrassLatticeUp
