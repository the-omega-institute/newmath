import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubjectReductionBundleTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubjectReductionBundleTraceUp : Type where
  | mk :
      (bundle setup extraction ledger transport route provenance name directRead : BHist) →
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

private theorem subjectReductionBundleTrace_decode_encode_bhist :
    ∀ h : BHist,
      subjectReductionBundleTraceDecodeBHist
          (subjectReductionBundleTraceEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def subjectReductionBundleTraceToEventFlow :
    SubjectReductionBundleTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubjectReductionBundleTraceUp.mk bundle setup extraction ledger transport route
      provenance name directRead =>
      [[BMark.b0],
        subjectReductionBundleTraceEncodeBHist bundle,
        [BMark.b1, BMark.b0],
        subjectReductionBundleTraceEncodeBHist setup,
        [BMark.b1, BMark.b1, BMark.b0],
        subjectReductionBundleTraceEncodeBHist extraction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionBundleTraceEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionBundleTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionBundleTraceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        subjectReductionBundleTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        subjectReductionBundleTraceEncodeBHist name,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        subjectReductionBundleTraceEncodeBHist directRead]

def subjectReductionBundleTraceFromEventFlow :
    EventFlow → Option SubjectReductionBundleTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag0 :: bundle :: _tag1 :: setup :: _tag2 :: extraction :: _tag3 :: ledger ::
      _tag4 :: transport :: _tag5 :: route :: _tag6 :: provenance :: _tag7 :: name ::
      _tag8 :: directRead :: [] =>
      some
        (SubjectReductionBundleTraceUp.mk
          (subjectReductionBundleTraceDecodeBHist bundle)
          (subjectReductionBundleTraceDecodeBHist setup)
          (subjectReductionBundleTraceDecodeBHist extraction)
          (subjectReductionBundleTraceDecodeBHist ledger)
          (subjectReductionBundleTraceDecodeBHist transport)
          (subjectReductionBundleTraceDecodeBHist route)
          (subjectReductionBundleTraceDecodeBHist provenance)
          (subjectReductionBundleTraceDecodeBHist name)
          (subjectReductionBundleTraceDecodeBHist directRead))
  | _ => none

private theorem subjectReductionBundleTrace_round_trip :
    ∀ x : SubjectReductionBundleTraceUp,
      subjectReductionBundleTraceFromEventFlow
          (subjectReductionBundleTraceToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk bundle setup extraction ledger transport route provenance name directRead =>
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
                (subjectReductionBundleTraceEncodeBHist name))
              (subjectReductionBundleTraceDecodeBHist
                (subjectReductionBundleTraceEncodeBHist directRead))) =
          some
            (SubjectReductionBundleTraceUp.mk bundle setup extraction ledger transport route
              provenance name directRead)
      rw [subjectReductionBundleTrace_decode_encode_bhist bundle,
        subjectReductionBundleTrace_decode_encode_bhist setup,
        subjectReductionBundleTrace_decode_encode_bhist extraction,
        subjectReductionBundleTrace_decode_encode_bhist ledger,
        subjectReductionBundleTrace_decode_encode_bhist transport,
        subjectReductionBundleTrace_decode_encode_bhist route,
        subjectReductionBundleTrace_decode_encode_bhist provenance,
        subjectReductionBundleTrace_decode_encode_bhist name,
        subjectReductionBundleTrace_decode_encode_bhist directRead]

private theorem subjectReductionBundleTraceToEventFlow_injective
    {x y : SubjectReductionBundleTraceUp} :
    subjectReductionBundleTraceToEventFlow x =
        subjectReductionBundleTraceToEventFlow y →
      x = y := by
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
          (subjectReductionBundleTraceToEventFlow x) =
        some x
    exact subjectReductionBundleTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (subjectReductionBundleTraceToEventFlow_injective heq)

instance subjectReductionBundleTraceFieldFaithful :
    FieldFaithful SubjectReductionBundleTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | SubjectReductionBundleTraceUp.mk bundle setup extraction ledger transport route
        provenance name directRead =>
        [bundle, setup, extraction, ledger, transport, route, provenance, name, directRead]
  field_faithful := by
    intro x y h
    cases x with
    | mk bundle1 setup1 extraction1 ledger1 transport1 route1 provenance1 name1
        directRead1 =>
        cases y with
        | mk bundle2 setup2 extraction2 ledger2 transport2 route2 provenance2 name2
            directRead2 =>
            injection h with hBundle t1
            injection t1 with hSetup t2
            injection t2 with hExtraction t3
            injection t3 with hLedger t4
            injection t4 with hTransport t5
            injection t5 with hRoute t6
            injection t6 with hProvenance t7
            injection t7 with hName t8
            injection t8 with hDirectRead _
            cases hBundle
            cases hSetup
            cases hExtraction
            cases hLedger
            cases hTransport
            cases hRoute
            cases hProvenance
            cases hName
            cases hDirectRead
            rfl

instance subjectReductionBundleTraceNontrivial :
    Nontrivial SubjectReductionBundleTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SubjectReductionBundleTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      SubjectReductionBundleTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SubjectReductionBundleTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  subjectReductionBundleTraceChapterTasteGate

end BEDC.Derived.SubjectReductionBundleTraceUp
