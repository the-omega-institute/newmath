import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RepresentedSpaceUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RepresentedSpaceUp : Type where
  | mk (S W Rho X T H C P N : BHist) : RepresentedSpaceUp
  deriving DecidableEq

def representedSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: representedSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: representedSpaceEncodeBHist h

def representedSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (representedSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (representedSpaceDecodeBHist tail)

private theorem RepresentedSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, representedSpaceDecodeBHist (representedSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def representedSpaceFields : RepresentedSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RepresentedSpaceUp.mk S W Rho X T H C P N => [S, W, Rho, X, T, H, C, P, N]

def representedSpaceToEventFlow : RepresentedSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map representedSpaceEncodeBHist (representedSpaceFields x)

private def representedSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => representedSpaceEventAt index rest

def representedSpaceFromEventFlow (ef : EventFlow) : Option RepresentedSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RepresentedSpaceUp.mk
      (representedSpaceDecodeBHist (representedSpaceEventAt 0 ef))
      (representedSpaceDecodeBHist (representedSpaceEventAt 1 ef))
      (representedSpaceDecodeBHist (representedSpaceEventAt 2 ef))
      (representedSpaceDecodeBHist (representedSpaceEventAt 3 ef))
      (representedSpaceDecodeBHist (representedSpaceEventAt 4 ef))
      (representedSpaceDecodeBHist (representedSpaceEventAt 5 ef))
      (representedSpaceDecodeBHist (representedSpaceEventAt 6 ef))
      (representedSpaceDecodeBHist (representedSpaceEventAt 7 ef))
      (representedSpaceDecodeBHist (representedSpaceEventAt 8 ef)))

private theorem RepresentedSpaceTasteGate_single_carrier_alignment_round_trip
    (x : RepresentedSpaceUp) :
    representedSpaceFromEventFlow (representedSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S W Rho X T H C P N =>
      change
        some
          (RepresentedSpaceUp.mk
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist S))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist W))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist Rho))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist X))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist T))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist H))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist C))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist P))
            (representedSpaceDecodeBHist (representedSpaceEncodeBHist N))) =
          some (RepresentedSpaceUp.mk S W Rho X T H C P N)
      rw [RepresentedSpaceTasteGate_single_carrier_alignment_decode S,
        RepresentedSpaceTasteGate_single_carrier_alignment_decode W,
        RepresentedSpaceTasteGate_single_carrier_alignment_decode Rho,
        RepresentedSpaceTasteGate_single_carrier_alignment_decode X,
        RepresentedSpaceTasteGate_single_carrier_alignment_decode T,
        RepresentedSpaceTasteGate_single_carrier_alignment_decode H,
        RepresentedSpaceTasteGate_single_carrier_alignment_decode C,
        RepresentedSpaceTasteGate_single_carrier_alignment_decode P,
        RepresentedSpaceTasteGate_single_carrier_alignment_decode N]

private theorem RepresentedSpaceTasteGate_single_carrier_alignment_injective
    {x y : RepresentedSpaceUp} :
    representedSpaceToEventFlow x = representedSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      representedSpaceFromEventFlow (representedSpaceToEventFlow x) =
        representedSpaceFromEventFlow (representedSpaceToEventFlow y) :=
    congrArg representedSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RepresentedSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RepresentedSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance representedSpaceBHistCarrier : BHistCarrier RepresentedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := representedSpaceToEventFlow
  fromEventFlow := representedSpaceFromEventFlow

instance representedSpaceChapterTasteGate : ChapterTasteGate RepresentedSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change representedSpaceFromEventFlow (representedSpaceToEventFlow x) = some x
    exact RepresentedSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RepresentedSpaceTasteGate_single_carrier_alignment_injective heq)

theorem RepresentedSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, representedSpaceDecodeBHist (representedSpaceEncodeBHist h) = h) ∧
      (∀ x : RepresentedSpaceUp,
        representedSpaceFromEventFlow (representedSpaceToEventFlow x) = some x) ∧
        (∀ x y : RepresentedSpaceUp,
          representedSpaceToEventFlow x = representedSpaceToEventFlow y → x = y) ∧
          representedSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RepresentedSpaceTasteGate_single_carrier_alignment_decode,
      RepresentedSpaceTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ h => RepresentedSpaceTasteGate_single_carrier_alignment_injective h),
      rfl⟩

end BEDC.Derived.RepresentedSpaceUp.TasteGate
