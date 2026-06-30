import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRealSubsequenceModulusUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRealSubsequenceModulusUp : Type where
  | mk
      (compactSource streamWindow bolzanoRoute modulus tolerance readback realSeal transport replay
        provenance localName : BHist) :
      CompactRealSubsequenceModulusUp
  deriving DecidableEq

def compactRealSubsequenceModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRealSubsequenceModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRealSubsequenceModulusEncodeBHist h

def compactRealSubsequenceModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRealSubsequenceModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRealSubsequenceModulusDecodeBHist tail)

private theorem CompactRealSubsequenceModulusTasteGate_decode_encode :
    ∀ h : BHist,
      compactRealSubsequenceModulusDecodeBHist
          (compactRealSubsequenceModulusEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compactRealSubsequenceModulusFields :
    CompactRealSubsequenceModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRealSubsequenceModulusUp.mk compactSource streamWindow bolzanoRoute modulus
      tolerance readback realSeal transport replay provenance localName =>
      [compactSource, streamWindow, bolzanoRoute, modulus, tolerance, readback, realSeal,
        transport, replay, provenance, localName]

def compactRealSubsequenceModulusToEventFlow :
    CompactRealSubsequenceModulusUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (compactRealSubsequenceModulusFields x).map compactRealSubsequenceModulusEncodeBHist

def compactRealSubsequenceModulusFromEventFlow :
    EventFlow → Option CompactRealSubsequenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun eventFlow =>
    match eventFlow with
    | [] => none
    | _ :: [] => none
    | _ :: _ :: [] => none
    | _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: [] => none
    | compactSource :: streamWindow :: bolzanoRoute :: modulus :: tolerance :: readback ::
        realSeal :: transport :: replay :: provenance :: localName :: [] =>
        some
          (CompactRealSubsequenceModulusUp.mk
            (compactRealSubsequenceModulusDecodeBHist compactSource)
            (compactRealSubsequenceModulusDecodeBHist streamWindow)
            (compactRealSubsequenceModulusDecodeBHist bolzanoRoute)
            (compactRealSubsequenceModulusDecodeBHist modulus)
            (compactRealSubsequenceModulusDecodeBHist tolerance)
            (compactRealSubsequenceModulusDecodeBHist readback)
            (compactRealSubsequenceModulusDecodeBHist realSeal)
            (compactRealSubsequenceModulusDecodeBHist transport)
            (compactRealSubsequenceModulusDecodeBHist replay)
            (compactRealSubsequenceModulusDecodeBHist provenance)
            (compactRealSubsequenceModulusDecodeBHist localName))
    | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ => none

def compactRealSubsequenceModulusBHistCarrier :
    BHistCarrier CompactRealSubsequenceModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRealSubsequenceModulusToEventFlow
  fromEventFlow := compactRealSubsequenceModulusFromEventFlow

instance compactRealSubsequenceModulusBHistCarrierInstance :
    BHistCarrier CompactRealSubsequenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactRealSubsequenceModulusBHistCarrier

private theorem CompactRealSubsequenceModulusTasteGate_round_trip :
    ∀ x : CompactRealSubsequenceModulusUp,
      compactRealSubsequenceModulusFromEventFlow
          (compactRealSubsequenceModulusToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk compactSource streamWindow bolzanoRoute modulus tolerance readback realSeal transport
      replay provenance localName =>
      change
        some
            (CompactRealSubsequenceModulusUp.mk
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist compactSource))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist streamWindow))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist bolzanoRoute))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist modulus))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist tolerance))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist readback))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist realSeal))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist transport))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist replay))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist provenance))
              (compactRealSubsequenceModulusDecodeBHist
                (compactRealSubsequenceModulusEncodeBHist localName))) =
          some
            (CompactRealSubsequenceModulusUp.mk compactSource streamWindow bolzanoRoute modulus
              tolerance readback realSeal transport replay provenance localName)
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode compactSource]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode streamWindow]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode bolzanoRoute]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode modulus]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode tolerance]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode readback]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode realSeal]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode transport]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode replay]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode provenance]
      rw [CompactRealSubsequenceModulusTasteGate_decode_encode localName]

private theorem CompactRealSubsequenceModulusTasteGate_toEventFlow_injective
    {x y : CompactRealSubsequenceModulusUp} :
    compactRealSubsequenceModulusToEventFlow x =
      compactRealSubsequenceModulusToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x =
          compactRealSubsequenceModulusFromEventFlow
            (compactRealSubsequenceModulusToEventFlow x) :=
        (CompactRealSubsequenceModulusTasteGate_round_trip x).symm
      _ =
          compactRealSubsequenceModulusFromEventFlow
            (compactRealSubsequenceModulusToEventFlow y) :=
        congrArg compactRealSubsequenceModulusFromEventFlow hxy
      _ = some y := CompactRealSubsequenceModulusTasteGate_round_trip y
  exact Option.some.inj optionEq

def compactRealSubsequenceModulusChapterTasteGate :
    @ChapterTasteGate CompactRealSubsequenceModulusUp
      compactRealSubsequenceModulusBHistCarrier where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactRealSubsequenceModulusFromEventFlow
          (compactRealSubsequenceModulusToEventFlow x) =
        some x
    exact CompactRealSubsequenceModulusTasteGate_round_trip x
  layer_separation := by
    intro x y hxy heq
    change compactRealSubsequenceModulusToEventFlow x =
      compactRealSubsequenceModulusToEventFlow y at heq
    exact hxy (CompactRealSubsequenceModulusTasteGate_toEventFlow_injective heq)

instance compactRealSubsequenceModulusChapterTasteGateInstance :
    ChapterTasteGate CompactRealSubsequenceModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactRealSubsequenceModulusChapterTasteGate

theorem CompactRealSubsequenceModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      compactRealSubsequenceModulusDecodeBHist (compactRealSubsequenceModulusEncodeBHist h) =
        h) ∧
      compactRealSubsequenceModulusEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · rfl

end BEDC.Derived.CompactRealSubsequenceModulusUp.TasteGate
