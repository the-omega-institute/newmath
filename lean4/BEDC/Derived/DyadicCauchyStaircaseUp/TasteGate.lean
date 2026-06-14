import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicCauchyStaircaseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicCauchyStaircaseUp : Type where
  | mk (S D L R E H C P N : BHist) : DyadicCauchyStaircaseUp
  deriving DecidableEq

def dyadicCauchyStaircaseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicCauchyStaircaseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicCauchyStaircaseEncodeBHist h

def dyadicCauchyStaircaseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicCauchyStaircaseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicCauchyStaircaseDecodeBHist tail)

private theorem DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicCauchyStaircaseFields : DyadicCauchyStaircaseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicCauchyStaircaseUp.mk S D L R E H C P N => [S, D, L, R, E, H, C, P, N]

def dyadicCauchyStaircaseToEventFlow : DyadicCauchyStaircaseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicCauchyStaircaseFields x).map dyadicCauchyStaircaseEncodeBHist

private def dyadicCauchyStaircaseEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dyadicCauchyStaircaseEventAt index rest

def dyadicCauchyStaircaseFromEventFlow (ef : EventFlow) :
    Option DyadicCauchyStaircaseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DyadicCauchyStaircaseUp.mk
      (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEventAt 0 ef))
      (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEventAt 1 ef))
      (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEventAt 2 ef))
      (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEventAt 3 ef))
      (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEventAt 4 ef))
      (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEventAt 5 ef))
      (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEventAt 6 ef))
      (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEventAt 7 ef))
      (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEventAt 8 ef)))

private theorem DyadicCauchyStaircaseTasteGate_single_carrier_alignment_round_trip
    (x : DyadicCauchyStaircaseUp) :
    dyadicCauchyStaircaseFromEventFlow (dyadicCauchyStaircaseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S D L R E H C P N =>
      change
        some
          (DyadicCauchyStaircaseUp.mk
            (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist S))
            (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist D))
            (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist L))
            (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist R))
            (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist E))
            (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist H))
            (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist C))
            (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist P))
            (dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist N))) =
          some (DyadicCauchyStaircaseUp.mk S D L R E H C P N)
      rw [DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode S,
        DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode D,
        DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode L,
        DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode R,
        DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode E,
        DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode H,
        DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode C,
        DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode P,
        DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode N]

private theorem DyadicCauchyStaircaseTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicCauchyStaircaseUp} :
    dyadicCauchyStaircaseToEventFlow x = dyadicCauchyStaircaseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicCauchyStaircaseFromEventFlow (dyadicCauchyStaircaseToEventFlow x) =
        dyadicCauchyStaircaseFromEventFlow (dyadicCauchyStaircaseToEventFlow y) :=
    congrArg dyadicCauchyStaircaseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicCauchyStaircaseTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicCauchyStaircaseTasteGate_single_carrier_alignment_round_trip y)))

instance dyadicCauchyStaircaseBHistCarrier : BHistCarrier DyadicCauchyStaircaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicCauchyStaircaseToEventFlow
  fromEventFlow := dyadicCauchyStaircaseFromEventFlow

instance dyadicCauchyStaircaseChapterTasteGate :
    ChapterTasteGate DyadicCauchyStaircaseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicCauchyStaircaseFromEventFlow (dyadicCauchyStaircaseToEventFlow x) = some x
    exact DyadicCauchyStaircaseTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicCauchyStaircaseTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem DyadicCauchyStaircaseTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier DyadicCauchyStaircaseUp) ∧
      Nonempty (ChapterTasteGate DyadicCauchyStaircaseUp) ∧
        (∀ h : BHist,
          dyadicCauchyStaircaseDecodeBHist (dyadicCauchyStaircaseEncodeBHist h) = h) ∧
          (∀ x : DyadicCauchyStaircaseUp,
            dyadicCauchyStaircaseFromEventFlow (dyadicCauchyStaircaseToEventFlow x) =
              some x) ∧
            dyadicCauchyStaircaseEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨dyadicCauchyStaircaseBHistCarrier⟩,
      ⟨dyadicCauchyStaircaseChapterTasteGate⟩,
      DyadicCauchyStaircaseTasteGate_single_carrier_alignment_decode,
      DyadicCauchyStaircaseTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.DyadicCauchyStaircaseUp
