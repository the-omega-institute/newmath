import BEDC.Derived.RadonMeasureUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RadonMeasureUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RadonMeasureUp : Type where
  | mk (X M O K V D H C P N : BHist) : RadonMeasureUp
  deriving DecidableEq

def radonMeasureEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: radonMeasureEncodeBHist h
  | BHist.e1 h => BMark.b1 :: radonMeasureEncodeBHist h

def radonMeasureDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (radonMeasureDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (radonMeasureDecodeBHist tail)

private theorem radonMeasureDecodeEncode :
    forall h : BHist, radonMeasureDecodeBHist (radonMeasureEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def radonMeasureFields : RadonMeasureUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RadonMeasureUp.mk X M O K V D H C P N => [X, M, O, K, V, D, H, C, P, N]

def radonMeasureToEventFlow : RadonMeasureUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (radonMeasureFields x).map radonMeasureEncodeBHist

def radonMeasureFromEventFlow : EventFlow → Option RadonMeasureUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | X :: M :: O :: K :: V :: D :: H :: C :: P :: N :: [] =>
      some
        (RadonMeasureUp.mk
          (radonMeasureDecodeBHist X)
          (radonMeasureDecodeBHist M)
          (radonMeasureDecodeBHist O)
          (radonMeasureDecodeBHist K)
          (radonMeasureDecodeBHist V)
          (radonMeasureDecodeBHist D)
          (radonMeasureDecodeBHist H)
          (radonMeasureDecodeBHist C)
          (radonMeasureDecodeBHist P)
          (radonMeasureDecodeBHist N))
  | _ => none

private theorem radonMeasureRoundTrip :
    forall x : RadonMeasureUp, radonMeasureFromEventFlow (radonMeasureToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X M O K V D H C P N =>
      simp only [radonMeasureToEventFlow, radonMeasureFields, radonMeasureFromEventFlow,
        List.map_cons, List.map_nil, radonMeasureDecodeEncode]

private theorem radonMeasureToEventFlow_injective {x y : RadonMeasureUp} :
    radonMeasureToEventFlow x = radonMeasureToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = radonMeasureFromEventFlow (radonMeasureToEventFlow x) :=
        (radonMeasureRoundTrip x).symm
      _ = radonMeasureFromEventFlow (radonMeasureToEventFlow y) :=
        congrArg radonMeasureFromEventFlow hxy
      _ = some y := radonMeasureRoundTrip y
  exact Option.some.inj optionEq

instance radonMeasureBHistCarrier : BHistCarrier RadonMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := radonMeasureToEventFlow
  fromEventFlow := radonMeasureFromEventFlow

instance radonMeasureChapterTasteGate : ChapterTasteGate RadonMeasureUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change radonMeasureFromEventFlow (radonMeasureToEventFlow x) = some x
    exact radonMeasureRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (radonMeasureToEventFlow_injective heq)

theorem RadonMeasureTasteGate_single_carrier_alignment :
    (forall h : BHist, radonMeasureDecodeBHist (radonMeasureEncodeBHist h) = h) ∧
      (forall X M O K V D H C P N : BHist,
        radonMeasureFields (RadonMeasureUp.mk X M O K V D H C P N) =
          [X, M, O, K, V, D, H, C, P, N]) ∧
        radonMeasureEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact ⟨radonMeasureDecodeEncode, (fun _ _ _ _ _ _ _ _ _ _ => rfl), rfl⟩

end BEDC.Derived.RadonMeasureUp.TasteGate
