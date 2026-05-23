import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompleteBaireSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompleteBaireSpaceUp : Type where
  | mk
      (baire metric stream readback completion trace transport replay provenance name :
        BHist) :
      CompleteBaireSpaceUp

def completeBaireSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: completeBaireSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: completeBaireSpaceEncodeBHist h

def completeBaireSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (completeBaireSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (completeBaireSpaceDecodeBHist tail)

private theorem completeBaireSpaceDecode_encode_bhist :
    ∀ h : BHist, completeBaireSpaceDecodeBHist (completeBaireSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem completeBaireSpace_mk_congr
    {baire baire' metric metric' stream stream' readback readback' completion completion' :
      BHist}
    {trace trace' transport transport' replay replay' provenance provenance' name name' :
      BHist}
    (hBaire : baire' = baire)
    (hMetric : metric' = metric)
    (hStream : stream' = stream)
    (hReadback : readback' = readback)
    (hCompletion : completion' = completion)
    (hTrace : trace' = trace)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    CompleteBaireSpaceUp.mk baire' metric' stream' readback' completion' trace' transport'
        replay' provenance' name' =
      CompleteBaireSpaceUp.mk baire metric stream readback completion trace transport replay
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hBaire
  cases hMetric
  cases hStream
  cases hReadback
  cases hCompletion
  cases hTrace
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def completeBaireSpaceFields : CompleteBaireSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompleteBaireSpaceUp.mk baire metric stream readback completion trace transport replay
      provenance name =>
      [baire, metric, stream, readback, completion, trace, transport, replay, provenance, name]

def completeBaireSpaceToEventFlow : CompleteBaireSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (completeBaireSpaceFields x).map completeBaireSpaceEncodeBHist

def completeBaireSpaceFromEventFlow : EventFlow → Option CompleteBaireSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _baire :: [] => none
  | _baire :: _metric :: [] => none
  | _baire :: _metric :: _stream :: [] => none
  | _baire :: _metric :: _stream :: _readback :: [] => none
  | _baire :: _metric :: _stream :: _readback :: _completion :: [] => none
  | _baire :: _metric :: _stream :: _readback :: _completion :: _trace :: [] => none
  | _baire :: _metric :: _stream :: _readback :: _completion :: _trace :: _transport ::
      [] => none
  | _baire :: _metric :: _stream :: _readback :: _completion :: _trace :: _transport ::
      _replay :: [] => none
  | _baire :: _metric :: _stream :: _readback :: _completion :: _trace :: _transport ::
      _replay :: _provenance :: [] => none
  | baire :: metric :: stream :: readback :: completion :: trace :: transport :: replay ::
      provenance :: name :: [] =>
      some
        (CompleteBaireSpaceUp.mk
          (completeBaireSpaceDecodeBHist baire)
          (completeBaireSpaceDecodeBHist metric)
          (completeBaireSpaceDecodeBHist stream)
          (completeBaireSpaceDecodeBHist readback)
          (completeBaireSpaceDecodeBHist completion)
          (completeBaireSpaceDecodeBHist trace)
          (completeBaireSpaceDecodeBHist transport)
          (completeBaireSpaceDecodeBHist replay)
          (completeBaireSpaceDecodeBHist provenance)
          (completeBaireSpaceDecodeBHist name))
  | _baire :: _metric :: _stream :: _readback :: _completion :: _trace :: _transport ::
      _replay :: _provenance :: _name :: _extra :: _rest => none

private theorem completeBaireSpace_round_trip :
    ∀ x : CompleteBaireSpaceUp,
      completeBaireSpaceFromEventFlow (completeBaireSpaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk baire metric stream readback completion trace transport replay provenance name =>
      exact
        congrArg some
          (completeBaireSpace_mk_congr
            (completeBaireSpaceDecode_encode_bhist baire)
            (completeBaireSpaceDecode_encode_bhist metric)
            (completeBaireSpaceDecode_encode_bhist stream)
            (completeBaireSpaceDecode_encode_bhist readback)
            (completeBaireSpaceDecode_encode_bhist completion)
            (completeBaireSpaceDecode_encode_bhist trace)
            (completeBaireSpaceDecode_encode_bhist transport)
            (completeBaireSpaceDecode_encode_bhist replay)
            (completeBaireSpaceDecode_encode_bhist provenance)
            (completeBaireSpaceDecode_encode_bhist name))

private theorem completeBaireSpaceToEventFlow_injective
    {x y : CompleteBaireSpaceUp} :
    completeBaireSpaceToEventFlow x = completeBaireSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      completeBaireSpaceFromEventFlow (completeBaireSpaceToEventFlow x) =
        completeBaireSpaceFromEventFlow (completeBaireSpaceToEventFlow y) :=
    congrArg completeBaireSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (completeBaireSpace_round_trip x).symm
      (Eq.trans hread (completeBaireSpace_round_trip y)))

private theorem completeBaireSpace_field_faithful :
    ∀ x y : CompleteBaireSpaceUp,
      completeBaireSpaceFields x = completeBaireSpaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk baire metric stream readback completion trace transport replay provenance name =>
      cases y with
      | mk baire' metric' stream' readback' completion' trace' transport' replay'
          provenance' name' =>
          cases hfields
          rfl

instance completeBaireSpaceBHistCarrier : BHistCarrier CompleteBaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := completeBaireSpaceToEventFlow
  fromEventFlow := completeBaireSpaceFromEventFlow

instance completeBaireSpaceChapterTasteGate : ChapterTasteGate CompleteBaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change completeBaireSpaceFromEventFlow (completeBaireSpaceToEventFlow x) = some x
    exact completeBaireSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (completeBaireSpaceToEventFlow_injective heq)

instance completeBaireSpaceFieldFaithful : FieldFaithful CompleteBaireSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := completeBaireSpaceFields
  field_faithful := completeBaireSpace_field_faithful

def taste_gate : ChapterTasteGate CompleteBaireSpaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  completeBaireSpaceChapterTasteGate

theorem CompleteBaireSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, completeBaireSpaceDecodeBHist (completeBaireSpaceEncodeBHist h) = h) ∧
      (∀ x : CompleteBaireSpaceUp,
        completeBaireSpaceFromEventFlow (completeBaireSpaceToEventFlow x) = some x) ∧
      (∀ x y : CompleteBaireSpaceUp,
        completeBaireSpaceToEventFlow x = completeBaireSpaceToEventFlow y → x = y) ∧
      completeBaireSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨completeBaireSpaceDecode_encode_bhist,
      completeBaireSpace_round_trip,
      (fun _ _ heq => completeBaireSpaceToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.CompleteBaireSpaceUp
