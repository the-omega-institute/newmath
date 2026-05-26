import BEDC.Derived.CauchyCompletionReflectorUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionReflectorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionReflectorUp : Type where
  | mk
      (source completionObject unit counit idempotent extension reflection transport
        componentTransport replay provenance localName : BHist) :
      CauchyCompletionReflectorUp
  deriving DecidableEq

def cauchyCompletionReflectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionReflectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionReflectorEncodeBHist h

def cauchyCompletionReflectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionReflectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionReflectorDecodeBHist tail)

private theorem CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionReflectorFields : CauchyCompletionReflectorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionReflectorUp.mk source completionObject unit counit idempotent
      extension reflection transport componentTransport replay provenance localName =>
      [source, completionObject, unit, counit, idempotent, extension, reflection, transport,
        componentTransport, replay, provenance, localName]

def cauchyCompletionReflectorToEventFlow : CauchyCompletionReflectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyCompletionReflectorFields x).map cauchyCompletionReflectorEncodeBHist

private def cauchyCompletionReflectorEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionReflectorEventAt index rest

def cauchyCompletionReflectorFromEventFlow
    (ef : EventFlow) : Option CauchyCompletionReflectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyCompletionReflectorUp.mk
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 0 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 1 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 2 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 3 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 4 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 5 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 6 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 7 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 8 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 9 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 10 ef))
      (cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEventAt 11 ef)))

private theorem CauchyCompletionReflectorTasteGate_single_carrier_alignment_round_trip
    (x : CauchyCompletionReflectorUp) :
    cauchyCompletionReflectorFromEventFlow (cauchyCompletionReflectorToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source completionObject unit counit idempotent extension reflection transport
      componentTransport replay provenance localName =>
      change
        some
          (CauchyCompletionReflectorUp.mk
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist source))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist completionObject))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist unit))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist counit))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist idempotent))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist extension))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist reflection))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist transport))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist componentTransport))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist replay))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist provenance))
            (cauchyCompletionReflectorDecodeBHist
              (cauchyCompletionReflectorEncodeBHist localName))) =
          some
            (CauchyCompletionReflectorUp.mk source completionObject unit counit idempotent
              extension reflection transport componentTransport replay provenance localName)
      rw [CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode source,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode
          completionObject,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode unit,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode counit,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode idempotent,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode extension,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode reflection,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode transport,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode
          componentTransport,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode replay,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode provenance,
        CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode localName]

private theorem CauchyCompletionReflectorToEventFlow_injective
    {x y : CauchyCompletionReflectorUp} :
    cauchyCompletionReflectorToEventFlow x = cauchyCompletionReflectorToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionReflectorFromEventFlow (cauchyCompletionReflectorToEventFlow x) =
        cauchyCompletionReflectorFromEventFlow (cauchyCompletionReflectorToEventFlow y) :=
    congrArg cauchyCompletionReflectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionReflectorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionReflectorTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionReflectorBHistCarrier :
    BHistCarrier CauchyCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionReflectorToEventFlow
  fromEventFlow := cauchyCompletionReflectorFromEventFlow

instance cauchyCompletionReflectorChapterTasteGate :
    ChapterTasteGate CauchyCompletionReflectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionReflectorFromEventFlow
          (cauchyCompletionReflectorToEventFlow x) =
        some x
    exact CauchyCompletionReflectorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyCompletionReflectorToEventFlow_injective heq)

theorem CauchyCompletionReflectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionReflectorDecodeBHist (cauchyCompletionReflectorEncodeBHist h) =
        h) ∧
      (∀ x : CauchyCompletionReflectorUp,
        cauchyCompletionReflectorFromEventFlow (cauchyCompletionReflectorToEventFlow x) =
          some x) ∧
        (∀ x y : CauchyCompletionReflectorUp,
          cauchyCompletionReflectorToEventFlow x = cauchyCompletionReflectorToEventFlow y →
            x = y) ∧
          cauchyCompletionReflectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionReflectorTasteGate_single_carrier_alignment_decode_encode,
      CauchyCompletionReflectorTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => CauchyCompletionReflectorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CauchyCompletionReflectorUp
