import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalSequenceSelectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalSequenceSelectorUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (index window monotonicity cofinalWindow filter subsequence readback realSeal
      transport replay provenance localName : BHist) : CofinalSequenceSelectorUp
  deriving DecidableEq

def cofinalSequenceSelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalSequenceSelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalSequenceSelectorEncodeBHist h

def cofinalSequenceSelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalSequenceSelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalSequenceSelectorDecodeBHist tail)

private theorem cofinalSequenceSelector_decode_encode :
    ∀ h : BHist,
      cofinalSequenceSelectorDecodeBHist
          (cofinalSequenceSelectorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cofinalSequenceSelectorFields :
    CofinalSequenceSelectorUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | CofinalSequenceSelectorUp.mk index window monotonicity cofinalWindow filter subsequence
      readback realSeal transport replay provenance localName =>
      [index, window, monotonicity, cofinalWindow, filter, subsequence, readback, realSeal,
        transport, replay, provenance, localName]

def cofinalSequenceSelectorToEventFlow :
    CofinalSequenceSelectorUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cofinalSequenceSelectorFields x).map cofinalSequenceSelectorEncodeBHist

def cofinalSequenceSelectorFromEventFlow :
    EventFlow → Option CofinalSequenceSelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | index :: window :: monotonicity :: cofinalWindow :: filter :: subsequence :: readback ::
      realSeal :: transport :: replay :: provenance :: localName :: [] =>
      some
        (CofinalSequenceSelectorUp.mk
          (cofinalSequenceSelectorDecodeBHist index)
          (cofinalSequenceSelectorDecodeBHist window)
          (cofinalSequenceSelectorDecodeBHist monotonicity)
          (cofinalSequenceSelectorDecodeBHist cofinalWindow)
          (cofinalSequenceSelectorDecodeBHist filter)
          (cofinalSequenceSelectorDecodeBHist subsequence)
          (cofinalSequenceSelectorDecodeBHist readback)
          (cofinalSequenceSelectorDecodeBHist realSeal)
          (cofinalSequenceSelectorDecodeBHist transport)
          (cofinalSequenceSelectorDecodeBHist replay)
          (cofinalSequenceSelectorDecodeBHist provenance)
          (cofinalSequenceSelectorDecodeBHist localName))
  | _ => none

private theorem cofinalSequenceSelector_round_trip :
    ∀ x : CofinalSequenceSelectorUp,
      cofinalSequenceSelectorFromEventFlow
          (cofinalSequenceSelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk index window monotonicity cofinalWindow filter subsequence readback realSeal
      transport replay provenance localName =>
      simp only [cofinalSequenceSelectorToEventFlow, cofinalSequenceSelectorFields,
        cofinalSequenceSelectorFromEventFlow, List.map_cons, List.map_nil,
        cofinalSequenceSelector_decode_encode]

private theorem cofinalSequenceSelectorToEventFlow_injective
    {x y : CofinalSequenceSelectorUp} :
    cofinalSequenceSelectorToEventFlow x =
        cofinalSequenceSelectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          cofinalSequenceSelectorFromEventFlow
            (cofinalSequenceSelectorToEventFlow x) :=
        (cofinalSequenceSelector_round_trip x).symm
      _ =
          cofinalSequenceSelectorFromEventFlow
            (cofinalSequenceSelectorToEventFlow y) :=
        congrArg cofinalSequenceSelectorFromEventFlow hxy
      _ = some y := cofinalSequenceSelector_round_trip y
  exact Option.some.inj optionEq

instance cofinalSequenceSelectorBHistCarrier :
    BHistCarrier CofinalSequenceSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalSequenceSelectorToEventFlow
  fromEventFlow := cofinalSequenceSelectorFromEventFlow

instance cofinalSequenceSelectorChapterTasteGate :
    ChapterTasteGate CofinalSequenceSelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cofinalSequenceSelectorFromEventFlow
          (cofinalSequenceSelectorToEventFlow x) =
        some x
    exact cofinalSequenceSelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalSequenceSelectorToEventFlow_injective heq)

end BEDC.Derived.CofinalSequenceSelectorUp
