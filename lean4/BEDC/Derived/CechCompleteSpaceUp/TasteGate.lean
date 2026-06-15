import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CechCompleteSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CechCompleteSpaceUp : Type where
  | mk (T U M F W S R H C P N : BHist) : CechCompleteSpaceUp

def cechCompleteSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cechCompleteSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cechCompleteSpaceEncodeBHist h

def cechCompleteSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cechCompleteSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cechCompleteSpaceDecodeBHist tail)

private theorem CechCompleteSpaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cechCompleteSpaceFields : CechCompleteSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CechCompleteSpaceUp.mk T U M F W S R H C P N =>
      [T, U, M, F, W, S, R, H, C, P, N]

def cechCompleteSpaceToEventFlow : CechCompleteSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cechCompleteSpaceFields x).map cechCompleteSpaceEncodeBHist

private def cechCompleteSpaceEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cechCompleteSpaceEventAtDefault index rest

def cechCompleteSpaceFromEventFlow (ef : EventFlow) : Option CechCompleteSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CechCompleteSpaceUp.mk
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 0 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 1 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 2 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 3 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 4 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 5 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 6 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 7 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 8 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 9 ef))
      (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEventAtDefault 10 ef)))

private theorem CechCompleteSpaceTasteGate_single_carrier_alignment_round_trip
    (x : CechCompleteSpaceUp) :
    cechCompleteSpaceFromEventFlow (cechCompleteSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T U M F W S R H C P N =>
      change
        some
          (CechCompleteSpaceUp.mk
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist T))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist U))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist M))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist F))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist W))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist S))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist R))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist H))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist C))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist P))
            (cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist N))) =
          some (CechCompleteSpaceUp.mk T U M F W S R H C P N)
      rw [CechCompleteSpaceTasteGate_single_carrier_alignment_decode T,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode U,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode M,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode F,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode W,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode S,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode R,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode H,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode C,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode P,
        CechCompleteSpaceTasteGate_single_carrier_alignment_decode N]

private theorem CechCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CechCompleteSpaceUp} :
    cechCompleteSpaceToEventFlow x = cechCompleteSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cechCompleteSpaceFromEventFlow (cechCompleteSpaceToEventFlow x) =
        cechCompleteSpaceFromEventFlow (cechCompleteSpaceToEventFlow y) :=
    congrArg cechCompleteSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CechCompleteSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CechCompleteSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance cechCompleteSpaceBHistCarrier : BHistCarrier CechCompleteSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cechCompleteSpaceToEventFlow
  fromEventFlow := cechCompleteSpaceFromEventFlow

instance cechCompleteSpaceChapterTasteGate : ChapterTasteGate CechCompleteSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cechCompleteSpaceFromEventFlow (cechCompleteSpaceToEventFlow x) = some x
    exact CechCompleteSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CechCompleteSpaceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CechCompleteSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cechCompleteSpaceChapterTasteGate

theorem CechCompleteSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, cechCompleteSpaceDecodeBHist (cechCompleteSpaceEncodeBHist h) = h) ∧
      (∀ x : CechCompleteSpaceUp,
        cechCompleteSpaceFromEventFlow (cechCompleteSpaceToEventFlow x) = some x) ∧
        Nonempty (BHistCarrier CechCompleteSpaceUp) ∧
          Nonempty (ChapterTasteGate CechCompleteSpaceUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CechCompleteSpaceTasteGate_single_carrier_alignment_decode,
      CechCompleteSpaceTasteGate_single_carrier_alignment_round_trip,
      ⟨cechCompleteSpaceBHistCarrier⟩,
      ⟨cechCompleteSpaceChapterTasteGate⟩⟩

end BEDC.Derived.CechCompleteSpaceUp
