import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyDiagonalArgumentUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyDiagonalArgumentUp : Type where
  | mk (R S T B L W Q E H C P N : BHist) : CauchyDiagonalArgumentUp

def cauchyDiagonalArgumentEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyDiagonalArgumentEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyDiagonalArgumentEncodeBHist h

def cauchyDiagonalArgumentDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyDiagonalArgumentDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyDiagonalArgumentDecodeBHist tail)

private theorem cauchyDiagonalArgument_decode_encode_bhist :
    ∀ h : BHist, cauchyDiagonalArgumentDecodeBHist
      (cauchyDiagonalArgumentEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyDiagonalArgumentToEventFlow : CauchyDiagonalArgumentUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyDiagonalArgumentUp.mk R S T B L W Q E H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b0],
        cauchyDiagonalArgumentEncodeBHist R,
        cauchyDiagonalArgumentEncodeBHist S,
        cauchyDiagonalArgumentEncodeBHist T,
        cauchyDiagonalArgumentEncodeBHist B,
        cauchyDiagonalArgumentEncodeBHist L,
        cauchyDiagonalArgumentEncodeBHist W,
        cauchyDiagonalArgumentEncodeBHist Q,
        cauchyDiagonalArgumentEncodeBHist E,
        cauchyDiagonalArgumentEncodeBHist H,
        cauchyDiagonalArgumentEncodeBHist C,
        cauchyDiagonalArgumentEncodeBHist P,
        cauchyDiagonalArgumentEncodeBHist N]

def cauchyDiagonalArgumentFromEventFlow : EventFlow → Option CauchyDiagonalArgumentUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: R :: S :: T :: B :: L :: W :: Q :: E :: H :: C :: P :: N :: [] =>
      some
        (CauchyDiagonalArgumentUp.mk
          (cauchyDiagonalArgumentDecodeBHist R)
          (cauchyDiagonalArgumentDecodeBHist S)
          (cauchyDiagonalArgumentDecodeBHist T)
          (cauchyDiagonalArgumentDecodeBHist B)
          (cauchyDiagonalArgumentDecodeBHist L)
          (cauchyDiagonalArgumentDecodeBHist W)
          (cauchyDiagonalArgumentDecodeBHist Q)
          (cauchyDiagonalArgumentDecodeBHist E)
          (cauchyDiagonalArgumentDecodeBHist H)
          (cauchyDiagonalArgumentDecodeBHist C)
          (cauchyDiagonalArgumentDecodeBHist P)
          (cauchyDiagonalArgumentDecodeBHist N))
  | _ => none

private theorem cauchyDiagonalArgument_round_trip :
    ∀ x : CauchyDiagonalArgumentUp,
      cauchyDiagonalArgumentFromEventFlow (cauchyDiagonalArgumentToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R S T B L W Q E H C P N =>
      simp only [cauchyDiagonalArgumentToEventFlow, cauchyDiagonalArgumentFromEventFlow,
        cauchyDiagonalArgument_decode_encode_bhist]

private theorem cauchyDiagonalArgumentToEventFlow_injective
    {x y : CauchyDiagonalArgumentUp} :
    cauchyDiagonalArgumentToEventFlow x = cauchyDiagonalArgumentToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyDiagonalArgumentFromEventFlow (cauchyDiagonalArgumentToEventFlow x) =
        cauchyDiagonalArgumentFromEventFlow (cauchyDiagonalArgumentToEventFlow y) :=
    congrArg cauchyDiagonalArgumentFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cauchyDiagonalArgument_round_trip x).symm
      (Eq.trans hread (cauchyDiagonalArgument_round_trip y)))

instance cauchyDiagonalArgumentBHistCarrier : BHistCarrier CauchyDiagonalArgumentUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyDiagonalArgumentToEventFlow
  fromEventFlow := cauchyDiagonalArgumentFromEventFlow

instance cauchyDiagonalArgumentChapterTasteGate :
    ChapterTasteGate CauchyDiagonalArgumentUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyDiagonalArgumentFromEventFlow
      (cauchyDiagonalArgumentToEventFlow x) = some x
    exact cauchyDiagonalArgument_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyDiagonalArgumentToEventFlow_injective heq)

def CauchyDiagonalArgumentTasteGate_single_carrier_alignment :
    @ChapterTasteGate CauchyDiagonalArgumentUp cauchyDiagonalArgumentBHistCarrier := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro x
    change cauchyDiagonalArgumentFromEventFlow
      (cauchyDiagonalArgumentToEventFlow x) = some x
    exact cauchyDiagonalArgument_round_trip x
  · intro x y hxy heq
    exact hxy (cauchyDiagonalArgumentToEventFlow_injective heq)

end BEDC.Derived.CauchyDiagonalArgumentUp
