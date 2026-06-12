import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ConstructiveRealLineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ConstructiveRealLineUp : Type where
  | mk (D S R E L A Delta I H C P N : BHist) : ConstructiveRealLineUp
  deriving DecidableEq

def constructiveRealLineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: constructiveRealLineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: constructiveRealLineEncodeBHist h

def constructiveRealLineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (constructiveRealLineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (constructiveRealLineDecodeBHist tail)

private theorem ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def constructiveRealLineFields : ConstructiveRealLineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ConstructiveRealLineUp.mk D S R E L A Delta I H C P N =>
      [D, S, R, E, L, A, Delta, I, H, C, P, N]

def constructiveRealLineToEventFlow : ConstructiveRealLineUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (constructiveRealLineFields x).map constructiveRealLineEncodeBHist

private def constructiveRealLineEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => constructiveRealLineEventAt index rest

def constructiveRealLineFromEventFlow (ef : EventFlow) : Option ConstructiveRealLineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ConstructiveRealLineUp.mk
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 0 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 1 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 2 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 3 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 4 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 5 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 6 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 7 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 8 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 9 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 10 ef))
      (constructiveRealLineDecodeBHist (constructiveRealLineEventAt 11 ef)))

private theorem ConstructiveRealLineTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ConstructiveRealLineUp,
      constructiveRealLineFromEventFlow (constructiveRealLineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R E L A Delta I H C P N =>
      change
        some
          (ConstructiveRealLineUp.mk
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist D))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist S))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist R))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist E))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist L))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist A))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist Delta))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist I))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist H))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist C))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist P))
            (constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist N))) =
          some (ConstructiveRealLineUp.mk D S R E L A Delta I H C P N)
      rw [ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode D,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode S,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode R,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode E,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode L,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode A,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode Delta,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode I,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode H,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode C,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode P,
        ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode N]

private theorem ConstructiveRealLineTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ConstructiveRealLineUp} :
    constructiveRealLineToEventFlow x = constructiveRealLineToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      constructiveRealLineFromEventFlow (constructiveRealLineToEventFlow x) =
        constructiveRealLineFromEventFlow (constructiveRealLineToEventFlow y) :=
    congrArg constructiveRealLineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ConstructiveRealLineTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ConstructiveRealLineTasteGate_single_carrier_alignment_round_trip y)))

instance constructiveRealLineBHistCarrier : BHistCarrier ConstructiveRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := constructiveRealLineToEventFlow
  fromEventFlow := constructiveRealLineFromEventFlow

instance constructiveRealLineChapterTasteGate : ChapterTasteGate ConstructiveRealLineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change constructiveRealLineFromEventFlow (constructiveRealLineToEventFlow x) = some x
    exact ConstructiveRealLineTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ConstructiveRealLineTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem ConstructiveRealLineTasteGate_single_carrier_alignment :
    (∀ h : BHist, constructiveRealLineDecodeBHist (constructiveRealLineEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ConstructiveRealLineUp) ∧
        Nonempty (ChapterTasteGate ConstructiveRealLineUp) ∧
          constructiveRealLineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ConstructiveRealLineTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨constructiveRealLineBHistCarrier⟩,
        ⟨⟨constructiveRealLineChapterTasteGate⟩, rfl⟩⟩⟩

end BEDC.Derived.ConstructiveRealLineUp
