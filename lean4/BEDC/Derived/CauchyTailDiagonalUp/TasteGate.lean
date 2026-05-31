import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyTailDiagonalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyTailDiagonalUp : Type where
  | mk (X Y delta W D E H C P N : BHist) : CauchyTailDiagonalUp
  deriving DecidableEq

def cauchyTailDiagonalEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyTailDiagonalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyTailDiagonalEncodeBHist h

def cauchyTailDiagonalDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyTailDiagonalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyTailDiagonalDecodeBHist tail)

private theorem CauchyTailDiagonalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyTailDiagonalFields : CauchyTailDiagonalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyTailDiagonalUp.mk X Y delta W D E H C P N =>
      [X, Y, delta, W, D, E, H, C, P, N]

def cauchyTailDiagonalToEventFlow : CauchyTailDiagonalUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyTailDiagonalFields x).map cauchyTailDiagonalEncodeBHist

private def CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt index rest

def cauchyTailDiagonalFromEventFlow (ef : EventFlow) : Option CauchyTailDiagonalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyTailDiagonalUp.mk
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 0 ef))
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 1 ef))
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 2 ef))
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 3 ef))
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 4 ef))
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 5 ef))
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 6 ef))
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 7 ef))
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 8 ef))
      (cauchyTailDiagonalDecodeBHist
        (CauchyTailDiagonalTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem CauchyTailDiagonalTasteGate_single_carrier_alignment_round_trip
    (x : CauchyTailDiagonalUp) :
    cauchyTailDiagonalFromEventFlow (cauchyTailDiagonalToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X Y delta W D E H C P N =>
      change
        some
          (CauchyTailDiagonalUp.mk
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist X))
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist Y))
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist delta))
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist W))
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist D))
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist E))
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist H))
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist C))
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist P))
            (cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist N))) =
          some (CauchyTailDiagonalUp.mk X Y delta W D E H C P N)
      rw [CauchyTailDiagonalTasteGate_single_carrier_alignment_decode X,
        CauchyTailDiagonalTasteGate_single_carrier_alignment_decode Y,
        CauchyTailDiagonalTasteGate_single_carrier_alignment_decode delta,
        CauchyTailDiagonalTasteGate_single_carrier_alignment_decode W,
        CauchyTailDiagonalTasteGate_single_carrier_alignment_decode D,
        CauchyTailDiagonalTasteGate_single_carrier_alignment_decode E,
        CauchyTailDiagonalTasteGate_single_carrier_alignment_decode H,
        CauchyTailDiagonalTasteGate_single_carrier_alignment_decode C,
        CauchyTailDiagonalTasteGate_single_carrier_alignment_decode P,
        CauchyTailDiagonalTasteGate_single_carrier_alignment_decode N]

private theorem CauchyTailDiagonalTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyTailDiagonalUp} :
    cauchyTailDiagonalToEventFlow x = cauchyTailDiagonalToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyTailDiagonalFromEventFlow (cauchyTailDiagonalToEventFlow x) =
        cauchyTailDiagonalFromEventFlow (cauchyTailDiagonalToEventFlow y) :=
    congrArg cauchyTailDiagonalFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyTailDiagonalTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyTailDiagonalTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyTailDiagonalBHistCarrier : BHistCarrier CauchyTailDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyTailDiagonalToEventFlow
  fromEventFlow := cauchyTailDiagonalFromEventFlow

instance cauchyTailDiagonalChapterTasteGate : ChapterTasteGate CauchyTailDiagonalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyTailDiagonalFromEventFlow (cauchyTailDiagonalToEventFlow x) = some x
    exact CauchyTailDiagonalTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyTailDiagonalTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem CauchyTailDiagonalTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyTailDiagonalDecodeBHist (cauchyTailDiagonalEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyTailDiagonalUp) ∧
        Nonempty (ChapterTasteGate CauchyTailDiagonalUp) ∧
          cauchyTailDiagonalEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyTailDiagonalTasteGate_single_carrier_alignment_decode,
      ⟨cauchyTailDiagonalBHistCarrier⟩,
      ⟨cauchyTailDiagonalChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyTailDiagonalUp
