import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LengthSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LengthSpaceUp : Type where
  | mk (M I A D S R T C P N : BHist) : LengthSpaceUp
  deriving DecidableEq

def lengthSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lengthSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lengthSpaceEncodeBHist h

def lengthSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lengthSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lengthSpaceDecodeBHist tail)

private theorem lengthSpaceDecodeEncode :
    ∀ h : BHist, lengthSpaceDecodeBHist (lengthSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lengthSpaceFields : LengthSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LengthSpaceUp.mk M I A D S R T C P N => [M, I, A, D, S, R, T, C, P, N]

def lengthSpaceToEventFlow : LengthSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lengthSpaceFields x).map lengthSpaceEncodeBHist

private def lengthSpaceEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lengthSpaceEventAt index rest

def lengthSpaceFromEventFlow (ef : EventFlow) : Option LengthSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LengthSpaceUp.mk
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 0 ef))
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 1 ef))
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 2 ef))
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 3 ef))
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 4 ef))
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 5 ef))
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 6 ef))
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 7 ef))
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 8 ef))
      (lengthSpaceDecodeBHist (lengthSpaceEventAt 9 ef)))

private theorem lengthSpaceRoundTrip (x : LengthSpaceUp) :
    lengthSpaceFromEventFlow (lengthSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk M I A D S R T C P N =>
      change
        some
          (LengthSpaceUp.mk
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist M))
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist I))
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist A))
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist D))
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist S))
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist R))
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist T))
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist C))
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist P))
            (lengthSpaceDecodeBHist (lengthSpaceEncodeBHist N))) =
          some (LengthSpaceUp.mk M I A D S R T C P N)
      rw [lengthSpaceDecodeEncode M,
        lengthSpaceDecodeEncode I,
        lengthSpaceDecodeEncode A,
        lengthSpaceDecodeEncode D,
        lengthSpaceDecodeEncode S,
        lengthSpaceDecodeEncode R,
        lengthSpaceDecodeEncode T,
        lengthSpaceDecodeEncode C,
        lengthSpaceDecodeEncode P,
        lengthSpaceDecodeEncode N]

private theorem lengthSpaceToEventFlow_injective {x y : LengthSpaceUp} :
    lengthSpaceToEventFlow x = lengthSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lengthSpaceFromEventFlow (lengthSpaceToEventFlow x) =
        lengthSpaceFromEventFlow (lengthSpaceToEventFlow y) :=
    congrArg lengthSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lengthSpaceRoundTrip x).symm
      (Eq.trans hread (lengthSpaceRoundTrip y)))

private theorem lengthSpaceFields_faithful :
    ∀ x y : LengthSpaceUp, lengthSpaceFields x = lengthSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M₁ I₁ A₁ D₁ S₁ R₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk M₂ I₂ A₂ D₂ S₂ R₂ T₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance lengthSpaceBHistCarrier : BHistCarrier LengthSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lengthSpaceToEventFlow
  fromEventFlow := lengthSpaceFromEventFlow

instance lengthSpaceChapterTasteGate : ChapterTasteGate LengthSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lengthSpaceFromEventFlow (lengthSpaceToEventFlow x) = some x
    exact lengthSpaceRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lengthSpaceToEventFlow_injective heq)

instance lengthSpaceFieldFaithful : FieldFaithful LengthSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lengthSpaceFields
  field_faithful := lengthSpaceFields_faithful

namespace TasteGate

theorem LengthSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, lengthSpaceDecodeBHist (lengthSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier LengthSpaceUp) ∧ Nonempty (ChapterTasteGate LengthSpaceUp) ∧
        lengthSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨lengthSpaceDecodeEncode,
      ⟨⟨lengthSpaceBHistCarrier⟩, ⟨lengthSpaceChapterTasteGate⟩, rfl⟩⟩

end TasteGate

end BEDC.Derived.LengthSpaceUp
