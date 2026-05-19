import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionBundleTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectReductionBundleTraceUp : Type where
  | mk (bundle setup extraction ledger transport route provenance name : BHist) :
      SubjectReductionBundleTraceUp
  deriving DecidableEq

def subjectReductionBundleTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: subjectReductionBundleTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: subjectReductionBundleTraceEncodeBHist h

def subjectReductionBundleTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (subjectReductionBundleTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (subjectReductionBundleTraceDecodeBHist tail)

private theorem subjectReductionBundleTraceDecode_encode_bhist :
    ∀ h : BHist,
      subjectReductionBundleTraceDecodeBHist
        (subjectReductionBundleTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def subjectReductionBundleTraceFields :
    SubjectReductionBundleTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionBundleTraceUp.mk bundle setup extraction ledger transport route provenance
      name =>
      [bundle, setup, extraction, ledger, transport, route, provenance, name]

def subjectReductionBundleTraceToEventFlow :
    SubjectReductionBundleTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (subjectReductionBundleTraceFields x).map subjectReductionBundleTraceEncodeBHist

def subjectReductionBundleTraceFromEventFlow :
    EventFlow → Option SubjectReductionBundleTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _bundle :: [] => none
  | _bundle :: _setup :: [] => none
  | _bundle :: _setup :: _extraction :: [] => none
  | _bundle :: _setup :: _extraction :: _ledger :: [] => none
  | _bundle :: _setup :: _extraction :: _ledger :: _transport :: [] => none
  | _bundle :: _setup :: _extraction :: _ledger :: _transport :: _route :: [] => none
  | _bundle :: _setup :: _extraction :: _ledger :: _transport :: _route :: _provenance ::
      [] => none
  | bundle :: setup :: extraction :: ledger :: transport :: route :: provenance :: name ::
      [] =>
      some
        (SubjectReductionBundleTraceUp.mk
          (subjectReductionBundleTraceDecodeBHist bundle)
          (subjectReductionBundleTraceDecodeBHist setup)
          (subjectReductionBundleTraceDecodeBHist extraction)
          (subjectReductionBundleTraceDecodeBHist ledger)
          (subjectReductionBundleTraceDecodeBHist transport)
          (subjectReductionBundleTraceDecodeBHist route)
          (subjectReductionBundleTraceDecodeBHist provenance)
          (subjectReductionBundleTraceDecodeBHist name))
  | _bundle :: _setup :: _extraction :: _ledger :: _transport :: _route :: _provenance ::
      _name :: _extra :: _rest => none

private theorem subjectReductionBundleTrace_round_trip :
    ∀ x : SubjectReductionBundleTraceUp,
      subjectReductionBundleTraceFromEventFlow
        (subjectReductionBundleTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bundle setup extraction ledger transport route provenance name =>
      change
        some
          (SubjectReductionBundleTraceUp.mk
            (subjectReductionBundleTraceDecodeBHist
              (subjectReductionBundleTraceEncodeBHist bundle))
            (subjectReductionBundleTraceDecodeBHist
              (subjectReductionBundleTraceEncodeBHist setup))
            (subjectReductionBundleTraceDecodeBHist
              (subjectReductionBundleTraceEncodeBHist extraction))
            (subjectReductionBundleTraceDecodeBHist
              (subjectReductionBundleTraceEncodeBHist ledger))
            (subjectReductionBundleTraceDecodeBHist
              (subjectReductionBundleTraceEncodeBHist transport))
            (subjectReductionBundleTraceDecodeBHist
              (subjectReductionBundleTraceEncodeBHist route))
            (subjectReductionBundleTraceDecodeBHist
              (subjectReductionBundleTraceEncodeBHist provenance))
            (subjectReductionBundleTraceDecodeBHist
              (subjectReductionBundleTraceEncodeBHist name))) =
          some
            (SubjectReductionBundleTraceUp.mk bundle setup extraction ledger transport route
              provenance name)
      rw [subjectReductionBundleTraceDecode_encode_bhist bundle,
        subjectReductionBundleTraceDecode_encode_bhist setup,
        subjectReductionBundleTraceDecode_encode_bhist extraction,
        subjectReductionBundleTraceDecode_encode_bhist ledger,
        subjectReductionBundleTraceDecode_encode_bhist transport,
        subjectReductionBundleTraceDecode_encode_bhist route,
        subjectReductionBundleTraceDecode_encode_bhist provenance,
        subjectReductionBundleTraceDecode_encode_bhist name]

private theorem subjectReductionBundleTraceToEventFlow_injective
    {x y : SubjectReductionBundleTraceUp} :
    subjectReductionBundleTraceToEventFlow x =
      subjectReductionBundleTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      subjectReductionBundleTraceFromEventFlow
          (subjectReductionBundleTraceToEventFlow x) =
        subjectReductionBundleTraceFromEventFlow
          (subjectReductionBundleTraceToEventFlow y) :=
    congrArg subjectReductionBundleTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (subjectReductionBundleTrace_round_trip x).symm
      (Eq.trans hread (subjectReductionBundleTrace_round_trip y)))

private theorem subjectReductionBundleTrace_fields_faithful :
    ∀ x y : SubjectReductionBundleTraceUp,
      subjectReductionBundleTraceFields x =
        subjectReductionBundleTraceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk bundle setup extraction ledger transport route provenance name =>
      cases y with
      | mk bundle' setup' extraction' ledger' transport' route' provenance' name' =>
          cases hfields
          rfl

instance subjectReductionBundleTraceBHistCarrier :
    BHistCarrier SubjectReductionBundleTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := subjectReductionBundleTraceToEventFlow
  fromEventFlow := subjectReductionBundleTraceFromEventFlow

instance subjectReductionBundleTraceChapterTasteGate :
    ChapterTasteGate SubjectReductionBundleTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      subjectReductionBundleTraceFromEventFlow
        (subjectReductionBundleTraceToEventFlow x) = some x
    exact subjectReductionBundleTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectReductionBundleTraceToEventFlow_injective heq)

instance subjectReductionBundleTraceFieldFaithful :
    FieldFaithful SubjectReductionBundleTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := subjectReductionBundleTraceFields
  field_faithful := subjectReductionBundleTrace_fields_faithful

instance subjectReductionBundleTraceNontrivial :
    BEDC.Meta.TasteGate.Nontrivial SubjectReductionBundleTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubjectReductionBundleTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SubjectReductionBundleTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SubjectReductionBundleTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subjectReductionBundleTraceChapterTasteGate

theorem SubjectReductionBundleTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        subjectReductionBundleTraceDecodeBHist
          (subjectReductionBundleTraceEncodeBHist h) = h) ∧
      (∀ x : SubjectReductionBundleTraceUp,
        subjectReductionBundleTraceFromEventFlow
          (subjectReductionBundleTraceToEventFlow x) = some x) ∧
      (∀ x y : SubjectReductionBundleTraceUp,
        subjectReductionBundleTraceToEventFlow x =
          subjectReductionBundleTraceToEventFlow y → x = y) ∧
      subjectReductionBundleTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨subjectReductionBundleTraceDecode_encode_bhist,
    subjectReductionBundleTrace_round_trip,
    fun _ _ heq => subjectReductionBundleTraceToEventFlow_injective heq,
    rfl⟩

end BEDC.Derived.SubjectReductionBundleTraceUp
