import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SeparatedUniformSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SeparatedUniformSpaceUp : Type where
  | mk (U D Z F H R C P N : BHist) : SeparatedUniformSpaceUp

def separatedUniformSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: separatedUniformSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: separatedUniformSpaceEncodeBHist h

def separatedUniformSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (separatedUniformSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (separatedUniformSpaceDecodeBHist tail)

private theorem separatedUniformSpace_decode_encode_bhist :
    ∀ h : BHist, separatedUniformSpaceDecodeBHist
      (separatedUniformSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def separatedUniformSpaceToEventFlow : SeparatedUniformSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SeparatedUniformSpaceUp.mk U D Z F H R C P N =>
      [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        separatedUniformSpaceEncodeBHist U,
        separatedUniformSpaceEncodeBHist D,
        separatedUniformSpaceEncodeBHist Z,
        separatedUniformSpaceEncodeBHist F,
        separatedUniformSpaceEncodeBHist H,
        separatedUniformSpaceEncodeBHist R,
        separatedUniformSpaceEncodeBHist C,
        separatedUniformSpaceEncodeBHist P,
        separatedUniformSpaceEncodeBHist N]

def separatedUniformSpaceFromEventFlow : EventFlow → Option SeparatedUniformSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: U :: D :: Z :: F :: H :: R :: C :: P :: N :: [] =>
      some
        (SeparatedUniformSpaceUp.mk
          (separatedUniformSpaceDecodeBHist U)
          (separatedUniformSpaceDecodeBHist D)
          (separatedUniformSpaceDecodeBHist Z)
          (separatedUniformSpaceDecodeBHist F)
          (separatedUniformSpaceDecodeBHist H)
          (separatedUniformSpaceDecodeBHist R)
          (separatedUniformSpaceDecodeBHist C)
          (separatedUniformSpaceDecodeBHist P)
          (separatedUniformSpaceDecodeBHist N))
  | _ => none

private theorem separatedUniformSpace_round_trip :
    ∀ x : SeparatedUniformSpaceUp,
      separatedUniformSpaceFromEventFlow (separatedUniformSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U D Z F H R C P N =>
      simp only [separatedUniformSpaceToEventFlow, separatedUniformSpaceFromEventFlow,
        separatedUniformSpace_decode_encode_bhist]

private theorem separatedUniformSpaceToEventFlow_injective {x y : SeparatedUniformSpaceUp} :
    separatedUniformSpaceToEventFlow x = separatedUniformSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      separatedUniformSpaceFromEventFlow (separatedUniformSpaceToEventFlow x) =
        separatedUniformSpaceFromEventFlow (separatedUniformSpaceToEventFlow y) :=
    congrArg separatedUniformSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (separatedUniformSpace_round_trip x).symm
      (Eq.trans hread (separatedUniformSpace_round_trip y)))

instance separatedUniformSpaceBHistCarrier : BHistCarrier SeparatedUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := separatedUniformSpaceToEventFlow
  fromEventFlow := separatedUniformSpaceFromEventFlow

instance separatedUniformSpaceChapterTasteGate :
    ChapterTasteGate SeparatedUniformSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change separatedUniformSpaceFromEventFlow (separatedUniformSpaceToEventFlow x) = some x
    exact separatedUniformSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (separatedUniformSpaceToEventFlow_injective heq)

def SeparatedUniformSpaceTasteGate_single_carrier_alignment :
    @ChapterTasteGate SeparatedUniformSpaceUp separatedUniformSpaceBHistCarrier := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change separatedUniformSpaceFromEventFlow (separatedUniformSpaceToEventFlow x) = some x
    exact separatedUniformSpace_round_trip x
  · intro x y hxy heq
    exact hxy (separatedUniformSpaceToEventFlow_injective heq)

end BEDC.Derived.SeparatedUniformSpaceUp
