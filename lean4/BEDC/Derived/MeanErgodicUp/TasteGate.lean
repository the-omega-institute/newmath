import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MeanErgodicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MeanErgodicUp : Type where
  | mk (E D W T H A P R C Q N : BHist) : MeanErgodicUp
  deriving DecidableEq

def meanErgodicEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: meanErgodicEncodeBHist h
  | BHist.e1 h => BMark.b1 :: meanErgodicEncodeBHist h

def meanErgodicDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (meanErgodicDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (meanErgodicDecodeBHist tail)

private theorem MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, meanErgodicDecodeBHist (meanErgodicEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def meanErgodicFields : MeanErgodicUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MeanErgodicUp.mk E D W T H A P R C Q N => [E, D, W, T, H, A, P, R, C, Q, N]

def meanErgodicToEventFlow : MeanErgodicUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (meanErgodicFields x).map meanErgodicEncodeBHist

private def meanErgodicRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _ => event
  | Nat.succ _, [] => []
  | Nat.succ index, _ :: rest => meanErgodicRawAt index rest

def meanErgodicFromEventFlow (flow : EventFlow) : Option MeanErgodicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (MeanErgodicUp.mk
      (meanErgodicDecodeBHist (meanErgodicRawAt 0 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 1 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 2 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 3 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 4 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 5 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 6 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 7 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 8 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 9 flow))
      (meanErgodicDecodeBHist (meanErgodicRawAt 10 flow)))

private theorem MeanErgodicUpTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MeanErgodicUp, meanErgodicFromEventFlow (meanErgodicToEventFlow x) = some x := by
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
      rw [MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode E,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode D,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode W,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode T,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode H,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode A,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode P,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode R,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode C,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode Q,
        MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode N]

private theorem MeanErgodicUpTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : MeanErgodicUp} :
    meanErgodicToEventFlow x = meanErgodicToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      meanErgodicFromEventFlow (meanErgodicToEventFlow x) =
        meanErgodicFromEventFlow (meanErgodicToEventFlow y) :=
    congrArg meanErgodicFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (MeanErgodicUpTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (MeanErgodicUpTasteGate_single_carrier_alignment_round_trip y)))

private theorem MeanErgodicUpTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : MeanErgodicUp, meanErgodicFields x = meanErgodicFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk E₁ D₁ W₁ T₁ H₁ A₁ P₁ R₁ C₁ Q₁ N₁ =>
      cases y with
      | mk E₂ D₂ W₂ T₂ H₂ A₂ P₂ R₂ C₂ Q₂ N₂ =>
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
    exact MeanErgodicUpTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (MeanErgodicUpTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance meanErgodicFieldFaithful : FieldFaithful MeanErgodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := meanErgodicFields
  field_faithful := MeanErgodicUpTasteGate_single_carrier_alignment_field_faithful

instance meanErgodicNontrivial : Nontrivial MeanErgodicUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MeanErgodicUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MeanErgodicUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MeanErgodicUp :=
  -- BEDC touchpoint anchor: BHist BMark
  meanErgodicChapterTasteGate

theorem MeanErgodicUpTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MeanErgodicUp) ∧
      Nonempty (FieldFaithful MeanErgodicUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial MeanErgodicUp) ∧
          (∀ h : BHist, meanErgodicDecodeBHist (meanErgodicEncodeBHist h) = h) ∧
            (∀ x : MeanErgodicUp, meanErgodicFromEventFlow (meanErgodicToEventFlow x) = some x) ∧
              (∀ x y : MeanErgodicUp,
                meanErgodicToEventFlow x = meanErgodicToEventFlow y → x = y) ∧
                meanErgodicEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨⟨meanErgodicChapterTasteGate⟩,
      ⟨⟨meanErgodicFieldFaithful⟩,
        ⟨⟨meanErgodicNontrivial⟩,
          ⟨MeanErgodicUpTasteGate_single_carrier_alignment_decode_encode,
            ⟨MeanErgodicUpTasteGate_single_carrier_alignment_round_trip,
              ⟨(fun _ _ heq =>
                  MeanErgodicUpTasteGate_single_carrier_alignment_toEventFlow_injective heq),
                rfl⟩⟩⟩⟩⟩⟩

end BEDC.Derived.MeanErgodicUp
