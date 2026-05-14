import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompileFrontierWitnessUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompileFrontierWitnessUp : Type where
  | mk :
      (source frontier compiler trace witness transport route provenance localName : BHist) →
        CompileFrontierWitnessUp
  deriving DecidableEq

def compileFrontierWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compileFrontierWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compileFrontierWitnessEncodeBHist h

def compileFrontierWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compileFrontierWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compileFrontierWitnessDecodeBHist tail)

private theorem CompileFrontierWitnessTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compileFrontierWitnessDecodeBHist
        (compileFrontierWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compileFrontierWitnessToEventFlow :
    CompileFrontierWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompileFrontierWitnessUp.mk source frontier compiler trace witness transport route
      provenance localName =>
      [[BMark.b0],
        compileFrontierWitnessEncodeBHist source,
        [BMark.b1, BMark.b0],
        compileFrontierWitnessEncodeBHist frontier,
        [BMark.b1, BMark.b1, BMark.b0],
        compileFrontierWitnessEncodeBHist compiler,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compileFrontierWitnessEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compileFrontierWitnessEncodeBHist witness,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compileFrontierWitnessEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compileFrontierWitnessEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compileFrontierWitnessEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compileFrontierWitnessEncodeBHist localName]

def compileFrontierWitnessFromEventFlow :
    EventFlow → Option CompileFrontierWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | frontier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | compiler :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | trace :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | witness :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | route :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16
                                                                        with
                                                                      | [] => none
                                                                      | localName ::
                                                                          rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] =>
                                                                              some
                                                                                (CompileFrontierWitnessUp.mk
                                                                                  (compileFrontierWitnessDecodeBHist
                                                                                    source)
                                                                                  (compileFrontierWitnessDecodeBHist
                                                                                    frontier)
                                                                                  (compileFrontierWitnessDecodeBHist
                                                                                    compiler)
                                                                                  (compileFrontierWitnessDecodeBHist
                                                                                    trace)
                                                                                  (compileFrontierWitnessDecodeBHist
                                                                                    witness)
                                                                                  (compileFrontierWitnessDecodeBHist
                                                                                    transport)
                                                                                  (compileFrontierWitnessDecodeBHist
                                                                                    route)
                                                                                  (compileFrontierWitnessDecodeBHist
                                                                                    provenance)
                                                                                  (compileFrontierWitnessDecodeBHist
                                                                                    localName))
                                                                          | _ :: _ => none

private theorem CompileFrontierWitnessTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompileFrontierWitnessUp,
      compileFrontierWitnessFromEventFlow
        (compileFrontierWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source frontier compiler trace witness transport route provenance localName =>
      change
        some
          (CompileFrontierWitnessUp.mk
            (compileFrontierWitnessDecodeBHist
              (compileFrontierWitnessEncodeBHist source))
            (compileFrontierWitnessDecodeBHist
              (compileFrontierWitnessEncodeBHist frontier))
            (compileFrontierWitnessDecodeBHist
              (compileFrontierWitnessEncodeBHist compiler))
            (compileFrontierWitnessDecodeBHist
              (compileFrontierWitnessEncodeBHist trace))
            (compileFrontierWitnessDecodeBHist
              (compileFrontierWitnessEncodeBHist witness))
            (compileFrontierWitnessDecodeBHist
              (compileFrontierWitnessEncodeBHist transport))
            (compileFrontierWitnessDecodeBHist
              (compileFrontierWitnessEncodeBHist route))
            (compileFrontierWitnessDecodeBHist
              (compileFrontierWitnessEncodeBHist provenance))
            (compileFrontierWitnessDecodeBHist
              (compileFrontierWitnessEncodeBHist localName))) =
          some
            (CompileFrontierWitnessUp.mk source frontier compiler trace witness
              transport route provenance localName)
      rw [CompileFrontierWitnessTasteGate_single_carrier_alignment_decode source,
        CompileFrontierWitnessTasteGate_single_carrier_alignment_decode frontier,
        CompileFrontierWitnessTasteGate_single_carrier_alignment_decode compiler,
        CompileFrontierWitnessTasteGate_single_carrier_alignment_decode trace,
        CompileFrontierWitnessTasteGate_single_carrier_alignment_decode witness,
        CompileFrontierWitnessTasteGate_single_carrier_alignment_decode transport,
        CompileFrontierWitnessTasteGate_single_carrier_alignment_decode route,
        CompileFrontierWitnessTasteGate_single_carrier_alignment_decode provenance,
        CompileFrontierWitnessTasteGate_single_carrier_alignment_decode localName]

private theorem CompileFrontierWitnessTasteGate_single_carrier_alignment_injective
    {x y : CompileFrontierWitnessUp} :
    compileFrontierWitnessToEventFlow x =
      compileFrontierWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compileFrontierWitnessFromEventFlow (compileFrontierWitnessToEventFlow x) =
        compileFrontierWitnessFromEventFlow (compileFrontierWitnessToEventFlow y) :=
    congrArg compileFrontierWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompileFrontierWitnessTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompileFrontierWitnessTasteGate_single_carrier_alignment_round_trip y)))

instance compileFrontierWitnessBHistCarrier :
    BHistCarrier CompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compileFrontierWitnessToEventFlow
  fromEventFlow := compileFrontierWitnessFromEventFlow

instance compileFrontierWitnessChapterTasteGate :
    ChapterTasteGate CompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compileFrontierWitnessFromEventFlow
        (compileFrontierWitnessToEventFlow x) = some x
    exact CompileFrontierWitnessTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompileFrontierWitnessTasteGate_single_carrier_alignment_injective heq)

instance compileFrontierWitnessFieldFaithful :
    FieldFaithful CompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CompileFrontierWitnessUp.mk source frontier compiler trace witness transport route
        provenance localName =>
        [source, frontier, compiler, trace, witness, transport, route, provenance,
          localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk source1 frontier1 compiler1 trace1 witness1 transport1 route1 provenance1
        localName1 =>
        cases y with
        | mk source2 frontier2 compiler2 trace2 witness2 transport2 route2 provenance2
            localName2 =>
            cases h
            rfl

instance compileFrontierWitnessNontrivial :
    Nontrivial CompileFrontierWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompileFrontierWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompileFrontierWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompileFrontierWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compileFrontierWitnessChapterTasteGate

theorem CompileFrontierWitnessTasteGate_single_carrier_alignment :
    (∀ h : BHist, compileFrontierWitnessDecodeBHist
      (compileFrontierWitnessEncodeBHist h) = h) ∧
      (∀ x : CompileFrontierWitnessUp, compileFrontierWitnessFromEventFlow
        (compileFrontierWitnessToEventFlow x) = some x) ∧
        (∀ x y : CompileFrontierWitnessUp,
          compileFrontierWitnessToEventFlow x =
            compileFrontierWitnessToEventFlow y → x = y) ∧
          Nonempty (ChapterTasteGate CompileFrontierWitnessUp) ∧
            Nonempty (FieldFaithful CompileFrontierWitnessUp) ∧
              Nonempty (Nontrivial CompileFrontierWitnessUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CompileFrontierWitnessTasteGate_single_carrier_alignment_decode
  · constructor
    · exact CompileFrontierWitnessTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact CompileFrontierWitnessTasteGate_single_carrier_alignment_injective heq
      · exact
          ⟨⟨compileFrontierWitnessChapterTasteGate⟩,
            ⟨compileFrontierWitnessFieldFaithful⟩,
            ⟨compileFrontierWitnessNontrivial⟩⟩

end BEDC.Derived.CompileFrontierWitnessUp.TasteGate

namespace BEDC.Derived.CompileFrontierWitnessUp

def taste_gate :
    BEDC.Meta.TasteGate.ChapterTasteGate TasteGate.CompileFrontierWitnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.CompileFrontierWitnessUp
