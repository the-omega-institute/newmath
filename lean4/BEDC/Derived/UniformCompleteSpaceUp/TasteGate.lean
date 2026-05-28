import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UniformCompleteSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UniformCompleteSpaceUp : Type where
  | mk (S F N M C Q R E H T P A : BHist) : UniformCompleteSpaceUp
  deriving DecidableEq

def uniformCompleteSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: uniformCompleteSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: uniformCompleteSpaceEncodeBHist h

def uniformCompleteSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (uniformCompleteSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (uniformCompleteSpaceDecodeBHist tail)

private theorem UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def uniformCompleteSpaceFields : UniformCompleteSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UniformCompleteSpaceUp.mk S F N M C Q R E H T P A => [S, F, N, M, C, Q, R, E, H, T, P, A]

def uniformCompleteSpaceToEventFlow : UniformCompleteSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (uniformCompleteSpaceFields x).map uniformCompleteSpaceEncodeBHist

private def uniformCompleteSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => uniformCompleteSpaceEventAt index rest

def uniformCompleteSpaceFromEventFlow (ef : EventFlow) : Option UniformCompleteSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (UniformCompleteSpaceUp.mk
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 0 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 1 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 2 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 3 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 4 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 5 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 6 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 7 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 8 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 9 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 10 ef))
      (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEventAt 11 ef)))

private theorem UniformCompleteSpaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : UniformCompleteSpaceUp,
      uniformCompleteSpaceFromEventFlow (uniformCompleteSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S F N M C Q R E H T P A =>
      change
        some
          (UniformCompleteSpaceUp.mk
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist S))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist F))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist N))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist M))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist C))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist Q))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist R))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist E))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist H))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist T))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist P))
            (uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist A))) =
          some (UniformCompleteSpaceUp.mk S F N M C Q R E H T P A)
      rw [UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode S,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode F,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode N,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode M,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode C,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode Q,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode R,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode E,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode H,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode T,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode P,
        UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode A]

private theorem UniformCompleteSpaceToEventFlow_injective
    {x y : UniformCompleteSpaceUp} :
    uniformCompleteSpaceToEventFlow x = uniformCompleteSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      uniformCompleteSpaceFromEventFlow (uniformCompleteSpaceToEventFlow x) =
        uniformCompleteSpaceFromEventFlow (uniformCompleteSpaceToEventFlow y) :=
    congrArg uniformCompleteSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (UniformCompleteSpaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (UniformCompleteSpaceTasteGate_single_carrier_alignment_round_trip y)))

instance uniformCompleteSpaceBHistCarrier : BHistCarrier UniformCompleteSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := uniformCompleteSpaceToEventFlow
  fromEventFlow := uniformCompleteSpaceFromEventFlow

instance uniformCompleteSpaceChapterTasteGate : ChapterTasteGate UniformCompleteSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change uniformCompleteSpaceFromEventFlow (uniformCompleteSpaceToEventFlow x) = some x
    exact UniformCompleteSpaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (UniformCompleteSpaceToEventFlow_injective heq)

def taste_gate : ChapterTasteGate UniformCompleteSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  uniformCompleteSpaceChapterTasteGate

theorem UniformCompleteSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, uniformCompleteSpaceDecodeBHist (uniformCompleteSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier UniformCompleteSpaceUp) ∧
        Nonempty (ChapterTasteGate UniformCompleteSpaceUp) ∧
          uniformCompleteSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨UniformCompleteSpaceTasteGate_single_carrier_alignment_decode_encode,
      ⟨uniformCompleteSpaceBHistCarrier⟩,
      ⟨uniformCompleteSpaceChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.UniformCompleteSpaceUp
