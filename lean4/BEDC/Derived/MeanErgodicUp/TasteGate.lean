import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MeanErgodicUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MeanErgodicUp : Type where
  | mk (E D W T H A P R C Q N : BHist) : MeanErgodicUp
  deriving DecidableEq

def meanErgodicEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: meanErgodicEncodeBHist h
  | BHist.e1 h => BMark.b1 :: meanErgodicEncodeBHist h

def meanErgodicDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (meanErgodicDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (meanErgodicDecodeBHist tail)

private theorem MeanErgodicTasteGate_single_carrier_alignment_decode :
    forall h : BHist, meanErgodicDecodeBHist (meanErgodicEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def meanErgodicFields : MeanErgodicUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MeanErgodicUp.mk E D W T H A P R C Q N => [E, D, W, T, H, A, P, R, C, Q, N]

def meanErgodicToEventFlow : MeanErgodicUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (meanErgodicFields x).map meanErgodicEncodeBHist

private def meanErgodicEventAtDefault : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => meanErgodicEventAtDefault index rest

def meanErgodicFromEventFlow (ef : EventFlow) : Option MeanErgodicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MeanErgodicUp.mk
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 0 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 1 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 2 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 3 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 4 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 5 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 6 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 7 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 8 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 9 ef))
      (meanErgodicDecodeBHist (meanErgodicEventAtDefault 10 ef)))

private theorem MeanErgodicTasteGate_single_carrier_alignment_round_trip :
    forall x : MeanErgodicUp,
      meanErgodicFromEventFlow (meanErgodicToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E D W T H A P R C Q N =>
      change
        some
          (MeanErgodicUp.mk
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist E))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist D))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist W))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist T))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist H))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist A))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist P))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist R))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist C))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist Q))
            (meanErgodicDecodeBHist (meanErgodicEncodeBHist N))) =
          some (MeanErgodicUp.mk E D W T H A P R C Q N)
      rw [MeanErgodicTasteGate_single_carrier_alignment_decode E,
        MeanErgodicTasteGate_single_carrier_alignment_decode D,
        MeanErgodicTasteGate_single_carrier_alignment_decode W,
        MeanErgodicTasteGate_single_carrier_alignment_decode T,
        MeanErgodicTasteGate_single_carrier_alignment_decode H,
        MeanErgodicTasteGate_single_carrier_alignment_decode A,
        MeanErgodicTasteGate_single_carrier_alignment_decode P,
        MeanErgodicTasteGate_single_carrier_alignment_decode R,
        MeanErgodicTasteGate_single_carrier_alignment_decode C,
        MeanErgodicTasteGate_single_carrier_alignment_decode Q,
        MeanErgodicTasteGate_single_carrier_alignment_decode N]

private theorem MeanErgodicTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MeanErgodicUp} :
    meanErgodicToEventFlow x = meanErgodicToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      meanErgodicFromEventFlow (meanErgodicToEventFlow x) =
        meanErgodicFromEventFlow (meanErgodicToEventFlow y) :=
    congrArg meanErgodicFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MeanErgodicTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MeanErgodicTasteGate_single_carrier_alignment_round_trip y)))

private theorem MeanErgodicTasteGate_single_carrier_alignment_fields :
    forall x y : MeanErgodicUp, meanErgodicFields x = meanErgodicFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance meanErgodicBHistCarrier : BHistCarrier MeanErgodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := meanErgodicToEventFlow
  fromEventFlow := meanErgodicFromEventFlow

instance meanErgodicChapterTasteGate : ChapterTasteGate MeanErgodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change meanErgodicFromEventFlow (meanErgodicToEventFlow x) = some x
    exact MeanErgodicTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MeanErgodicTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance meanErgodicFieldFaithful : FieldFaithful MeanErgodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := meanErgodicFields
  field_faithful := MeanErgodicTasteGate_single_carrier_alignment_fields

instance meanErgodicNontrivial : Nontrivial MeanErgodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MeanErgodicUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MeanErgodicUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem MeanErgodicTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MeanErgodicUp) ∧
      Nonempty (FieldFaithful MeanErgodicUp) ∧
      Nonempty (BEDC.Meta.TasteGate.Nontrivial MeanErgodicUp) ∧
      (∀ h : BHist, meanErgodicDecodeBHist (meanErgodicEncodeBHist h) = h) ∧
      (∀ x : MeanErgodicUp,
        meanErgodicFromEventFlow (meanErgodicToEventFlow x) = some x) ∧
      (∀ x y : MeanErgodicUp,
        meanErgodicToEventFlow x = meanErgodicToEventFlow y -> x = y) ∧
      meanErgodicEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨meanErgodicChapterTasteGate⟩,
      ⟨meanErgodicFieldFaithful⟩,
      ⟨meanErgodicNontrivial⟩,
      MeanErgodicTasteGate_single_carrier_alignment_decode,
      MeanErgodicTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => MeanErgodicTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.MeanErgodicUp.TasteGate
