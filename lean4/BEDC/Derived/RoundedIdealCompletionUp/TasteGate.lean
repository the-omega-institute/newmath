import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RoundedIdealCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RoundedIdealCompletionUp : Type where
  | mk
      (metric formalBall dyadic stream rounded directed transport replay provenance name :
        BHist) :
      RoundedIdealCompletionUp

def roundedIdealCompletionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: roundedIdealCompletionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: roundedIdealCompletionEncodeBHist h

def roundedIdealCompletionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (roundedIdealCompletionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (roundedIdealCompletionDecodeBHist tail)

private theorem roundedIdealCompletionDecode_encode_bhist :
    ∀ h : BHist,
      roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem roundedIdealCompletion_mk_congr
    {metric metric' formalBall formalBall' dyadic dyadic' stream stream' rounded rounded' :
      BHist}
    {directed directed' transport transport' replay replay' provenance provenance' name name' :
      BHist}
    (hMetric : metric' = metric)
    (hFormalBall : formalBall' = formalBall)
    (hDyadic : dyadic' = dyadic)
    (hStream : stream' = stream)
    (hRounded : rounded' = rounded)
    (hDirected : directed' = directed)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RoundedIdealCompletionUp.mk metric' formalBall' dyadic' stream' rounded' directed'
        transport' replay' provenance' name' =
      RoundedIdealCompletionUp.mk metric formalBall dyadic stream rounded directed transport
        replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hMetric
  cases hFormalBall
  cases hDyadic
  cases hStream
  cases hRounded
  cases hDirected
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def roundedIdealCompletionFields : RoundedIdealCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RoundedIdealCompletionUp.mk metric formalBall dyadic stream rounded directed transport
      replay provenance name =>
      [metric, formalBall, dyadic, stream, rounded, directed, transport, replay, provenance,
        name]

def roundedIdealCompletionToEventFlow : RoundedIdealCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (roundedIdealCompletionFields x).map roundedIdealCompletionEncodeBHist

def roundedIdealCompletionFromEventFlow : EventFlow → Option RoundedIdealCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _metric :: [] => none
  | _metric :: _formalBall :: [] => none
  | _metric :: _formalBall :: _dyadic :: [] => none
  | _metric :: _formalBall :: _dyadic :: _stream :: [] => none
  | _metric :: _formalBall :: _dyadic :: _stream :: _rounded :: [] => none
  | _metric :: _formalBall :: _dyadic :: _stream :: _rounded :: _directed :: [] => none
  | _metric :: _formalBall :: _dyadic :: _stream :: _rounded :: _directed ::
      _transport :: [] => none
  | _metric :: _formalBall :: _dyadic :: _stream :: _rounded :: _directed ::
      _transport :: _replay :: [] => none
  | _metric :: _formalBall :: _dyadic :: _stream :: _rounded :: _directed ::
      _transport :: _replay :: _provenance :: [] => none
  | metric :: formalBall :: dyadic :: stream :: rounded :: directed :: transport ::
      replay :: provenance :: name :: [] =>
      some
        (RoundedIdealCompletionUp.mk
          (roundedIdealCompletionDecodeBHist metric)
          (roundedIdealCompletionDecodeBHist formalBall)
          (roundedIdealCompletionDecodeBHist dyadic)
          (roundedIdealCompletionDecodeBHist stream)
          (roundedIdealCompletionDecodeBHist rounded)
          (roundedIdealCompletionDecodeBHist directed)
          (roundedIdealCompletionDecodeBHist transport)
          (roundedIdealCompletionDecodeBHist replay)
          (roundedIdealCompletionDecodeBHist provenance)
          (roundedIdealCompletionDecodeBHist name))
  | _metric :: _formalBall :: _dyadic :: _stream :: _rounded :: _directed :: _transport ::
      _replay :: _provenance :: _name :: _extra :: _rest => none

private theorem roundedIdealCompletion_round_trip :
    ∀ x : RoundedIdealCompletionUp,
      roundedIdealCompletionFromEventFlow (roundedIdealCompletionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk metric formalBall dyadic stream rounded directed transport replay provenance name =>
      exact
        congrArg some
          (roundedIdealCompletion_mk_congr
            (roundedIdealCompletionDecode_encode_bhist metric)
            (roundedIdealCompletionDecode_encode_bhist formalBall)
            (roundedIdealCompletionDecode_encode_bhist dyadic)
            (roundedIdealCompletionDecode_encode_bhist stream)
            (roundedIdealCompletionDecode_encode_bhist rounded)
            (roundedIdealCompletionDecode_encode_bhist directed)
            (roundedIdealCompletionDecode_encode_bhist transport)
            (roundedIdealCompletionDecode_encode_bhist replay)
            (roundedIdealCompletionDecode_encode_bhist provenance)
            (roundedIdealCompletionDecode_encode_bhist name))

private theorem roundedIdealCompletionToEventFlow_injective
    {x y : RoundedIdealCompletionUp} :
    roundedIdealCompletionToEventFlow x = roundedIdealCompletionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      roundedIdealCompletionFromEventFlow (roundedIdealCompletionToEventFlow x) =
        roundedIdealCompletionFromEventFlow (roundedIdealCompletionToEventFlow y) :=
    congrArg roundedIdealCompletionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (roundedIdealCompletion_round_trip x).symm
      (Eq.trans hread (roundedIdealCompletion_round_trip y)))

private theorem roundedIdealCompletion_field_faithful :
    ∀ x y : RoundedIdealCompletionUp,
      roundedIdealCompletionFields x = roundedIdealCompletionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk metric formalBall dyadic stream rounded directed transport replay provenance name =>
      cases y with
      | mk metric' formalBall' dyadic' stream' rounded' directed' transport' replay'
          provenance' name' =>
          cases hfields
          rfl

instance roundedIdealCompletionBHistCarrier : BHistCarrier RoundedIdealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := roundedIdealCompletionToEventFlow
  fromEventFlow := roundedIdealCompletionFromEventFlow

instance roundedIdealCompletionChapterTasteGate :
    ChapterTasteGate RoundedIdealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change roundedIdealCompletionFromEventFlow (roundedIdealCompletionToEventFlow x) = some x
    exact roundedIdealCompletion_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (roundedIdealCompletionToEventFlow_injective heq)

instance roundedIdealCompletionFieldFaithful : FieldFaithful RoundedIdealCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := roundedIdealCompletionFields
  field_faithful := roundedIdealCompletion_field_faithful

def taste_gate : ChapterTasteGate RoundedIdealCompletionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  roundedIdealCompletionChapterTasteGate

theorem RoundedIdealCompletionTasteGate_single_carrier_alignment :
    (∀ h : BHist, roundedIdealCompletionDecodeBHist (roundedIdealCompletionEncodeBHist h) = h) ∧
      (∀ x : RoundedIdealCompletionUp,
        roundedIdealCompletionFromEventFlow (roundedIdealCompletionToEventFlow x) = some x) ∧
      (∀ x y : RoundedIdealCompletionUp,
        roundedIdealCompletionToEventFlow x = roundedIdealCompletionToEventFlow y → x = y) ∧
      roundedIdealCompletionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨roundedIdealCompletionDecode_encode_bhist,
      roundedIdealCompletion_round_trip,
      (fun _ _ heq => roundedIdealCompletionToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RoundedIdealCompletionUp
