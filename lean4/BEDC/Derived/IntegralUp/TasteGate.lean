import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.IntegralUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive IntegralUp : Type where
  | mk
      (function measure classifier operation ledger transport replay provenance localName :
        BHist) : IntegralUp
  deriving DecidableEq

def integralEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: integralEncodeBHist h
  | BHist.e1 h => BMark.b1 :: integralEncodeBHist h

def integralDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (integralDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (integralDecodeBHist tail)

private theorem IntegralTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, integralDecodeBHist (integralEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def IntegralTasteGate_single_carrier_alignment_fields :
    IntegralUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | IntegralUp.mk function measure classifier operation ledger transport replay provenance
      localName =>
      [function, measure, classifier, operation, ledger, transport, replay, provenance,
        localName]

def IntegralTasteGate_single_carrier_alignment_toEventFlow :
    IntegralUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (IntegralTasteGate_single_carrier_alignment_fields x).map integralEncodeBHist

def IntegralTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option IntegralUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | function :: measure :: classifier :: operation :: ledger :: transport :: replay ::
      provenance :: localName :: [] =>
      some
        (IntegralUp.mk
          (integralDecodeBHist function)
          (integralDecodeBHist measure)
          (integralDecodeBHist classifier)
          (integralDecodeBHist operation)
          (integralDecodeBHist ledger)
          (integralDecodeBHist transport)
          (integralDecodeBHist replay)
          (integralDecodeBHist provenance)
          (integralDecodeBHist localName))
  | _ => none

private theorem IntegralTasteGate_single_carrier_alignment_round_trip :
    ∀ x : IntegralUp,
      IntegralTasteGate_single_carrier_alignment_fromEventFlow
          (IntegralTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk function measure classifier operation ledger transport replay provenance localName =>
      change
        some
          (IntegralUp.mk
            (integralDecodeBHist (integralEncodeBHist function))
            (integralDecodeBHist (integralEncodeBHist measure))
            (integralDecodeBHist (integralEncodeBHist classifier))
            (integralDecodeBHist (integralEncodeBHist operation))
            (integralDecodeBHist (integralEncodeBHist ledger))
            (integralDecodeBHist (integralEncodeBHist transport))
            (integralDecodeBHist (integralEncodeBHist replay))
            (integralDecodeBHist (integralEncodeBHist provenance))
            (integralDecodeBHist (integralEncodeBHist localName))) =
          some
            (IntegralUp.mk function measure classifier operation ledger transport replay
              provenance localName)
      rw [IntegralTasteGate_single_carrier_alignment_decode_encode function,
        IntegralTasteGate_single_carrier_alignment_decode_encode measure,
        IntegralTasteGate_single_carrier_alignment_decode_encode classifier,
        IntegralTasteGate_single_carrier_alignment_decode_encode operation,
        IntegralTasteGate_single_carrier_alignment_decode_encode ledger,
        IntegralTasteGate_single_carrier_alignment_decode_encode transport,
        IntegralTasteGate_single_carrier_alignment_decode_encode replay,
        IntegralTasteGate_single_carrier_alignment_decode_encode provenance,
        IntegralTasteGate_single_carrier_alignment_decode_encode localName]

private theorem IntegralTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : IntegralUp} :
    IntegralTasteGate_single_carrier_alignment_toEventFlow x =
        IntegralTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      IntegralTasteGate_single_carrier_alignment_fromEventFlow
          (IntegralTasteGate_single_carrier_alignment_toEventFlow x) =
        IntegralTasteGate_single_carrier_alignment_fromEventFlow
          (IntegralTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg IntegralTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (IntegralTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (IntegralTasteGate_single_carrier_alignment_round_trip y)))

instance IntegralTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier IntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := IntegralTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := IntegralTasteGate_single_carrier_alignment_fromEventFlow

instance IntegralTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate IntegralUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      IntegralTasteGate_single_carrier_alignment_fromEventFlow
          (IntegralTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact IntegralTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (IntegralTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem IntegralTasteGate_single_carrier_alignment :
    (∀ h : BHist, integralDecodeBHist (integralEncodeBHist h) = h) ∧
      IntegralTasteGate_single_carrier_alignment_fields
          (IntegralUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · rfl

end BEDC.Derived.IntegralUp
