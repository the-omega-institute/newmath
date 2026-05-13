import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SubstitutionAuditMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SubstitutionAuditMapUp : Type where
  | mk :
      (term closed shift substitute composition generator transport route provenance name :
        BHist) →
        SubstitutionAuditMapUp
  deriving DecidableEq

def substitutionAuditMapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: substitutionAuditMapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: substitutionAuditMapEncodeBHist h

def substitutionAuditMapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (substitutionAuditMapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (substitutionAuditMapDecodeBHist tail)

private theorem SubstitutionAuditMapTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem SubstitutionAuditMapTasteGate_single_carrier_alignment_mk_congr
    {term term' closed closed' shift shift' substitute substitute' composition
      composition' generator generator' transport transport' route route' provenance
      provenance' name name' : BHist}
    (hTerm : term' = term)
    (hClosed : closed' = closed)
    (hShift : shift' = shift)
    (hSubstitute : substitute' = substitute)
    (hComposition : composition' = composition)
    (hGenerator : generator' = generator)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    SubstitutionAuditMapUp.mk term' closed' shift' substitute' composition' generator'
        transport' route' provenance' name' =
      SubstitutionAuditMapUp.mk term closed shift substitute composition generator transport
        route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hTerm
  cases hClosed
  cases hShift
  cases hSubstitute
  cases hComposition
  cases hGenerator
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def substitutionAuditMapToEventFlow : SubstitutionAuditMapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | SubstitutionAuditMapUp.mk term closed shift substitute composition generator transport
      route provenance name =>
      [[BMark.b0],
        substitutionAuditMapEncodeBHist term,
        [BMark.b1, BMark.b0],
        substitutionAuditMapEncodeBHist closed,
        [BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditMapEncodeBHist shift,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditMapEncodeBHist substitute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditMapEncodeBHist composition,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditMapEncodeBHist generator,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditMapEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        substitutionAuditMapEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        substitutionAuditMapEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        substitutionAuditMapEncodeBHist name]

def substitutionAuditMapFromEventFlow :
    EventFlow → Option SubstitutionAuditMapUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | term :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | closed :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | shift :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | substitute :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | composition :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | generator :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | route :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | name :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (SubstitutionAuditMapUp.mk
                                                                                          (substitutionAuditMapDecodeBHist term)
                                                                                          (substitutionAuditMapDecodeBHist closed)
                                                                                          (substitutionAuditMapDecodeBHist shift)
                                                                                          (substitutionAuditMapDecodeBHist substitute)
                                                                                          (substitutionAuditMapDecodeBHist composition)
                                                                                          (substitutionAuditMapDecodeBHist generator)
                                                                                          (substitutionAuditMapDecodeBHist transport)
                                                                                          (substitutionAuditMapDecodeBHist route)
                                                                                          (substitutionAuditMapDecodeBHist provenance)
                                                                                          (substitutionAuditMapDecodeBHist name))
                                                                                  | _ :: _ => none

private theorem SubstitutionAuditMapTasteGate_single_carrier_alignment_round :
    ∀ x : SubstitutionAuditMapUp,
      substitutionAuditMapFromEventFlow
        (substitutionAuditMapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk term closed shift substitute composition generator transport route provenance name =>
      change
        some
          (SubstitutionAuditMapUp.mk
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist term))
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist closed))
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist shift))
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist substitute))
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist composition))
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist generator))
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist transport))
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist route))
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist provenance))
            (substitutionAuditMapDecodeBHist (substitutionAuditMapEncodeBHist name))) =
          some
            (SubstitutionAuditMapUp.mk term closed shift substitute composition generator
              transport route provenance name)
      exact
        congrArg some
          (SubstitutionAuditMapTasteGate_single_carrier_alignment_mk_congr
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode term)
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode closed)
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode shift)
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode substitute)
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode composition)
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode generator)
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode transport)
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode route)
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode provenance)
            (SubstitutionAuditMapTasteGate_single_carrier_alignment_decode name))

private theorem SubstitutionAuditMapTasteGate_single_carrier_alignment_injective
    {x y : SubstitutionAuditMapUp} :
    substitutionAuditMapToEventFlow x = substitutionAuditMapToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      substitutionAuditMapFromEventFlow (substitutionAuditMapToEventFlow x) =
        substitutionAuditMapFromEventFlow (substitutionAuditMapToEventFlow y) :=
    congrArg substitutionAuditMapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (SubstitutionAuditMapTasteGate_single_carrier_alignment_round x).symm
      (Eq.trans hread (SubstitutionAuditMapTasteGate_single_carrier_alignment_round y)))

instance substitutionAuditMapBHistCarrier :
    BHistCarrier SubstitutionAuditMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := substitutionAuditMapToEventFlow
  fromEventFlow := substitutionAuditMapFromEventFlow

instance substitutionAuditMapChapterTasteGate :
    ChapterTasteGate SubstitutionAuditMapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      substitutionAuditMapFromEventFlow (substitutionAuditMapToEventFlow x) = some x
    exact SubstitutionAuditMapTasteGate_single_carrier_alignment_round x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SubstitutionAuditMapTasteGate_single_carrier_alignment_injective heq)

theorem taste_gate : ChapterTasteGate SubstitutionAuditMapUp := by
  exact inferInstance

theorem SubstitutionAuditMapTasteGate_single_carrier_alignment :
    (forall h : BHist, substitutionAuditMapDecodeBHist
      (substitutionAuditMapEncodeBHist h) = h) /\
      (forall x : SubstitutionAuditMapUp, substitutionAuditMapFromEventFlow
        (substitutionAuditMapToEventFlow x) = some x) /\
        (forall x y : SubstitutionAuditMapUp, substitutionAuditMapToEventFlow x =
          substitutionAuditMapToEventFlow y -> x = y) /\
          substitutionAuditMapEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact SubstitutionAuditMapTasteGate_single_carrier_alignment_decode
  · constructor
    · exact SubstitutionAuditMapTasteGate_single_carrier_alignment_round
    · constructor
      · intro x y heq
        exact SubstitutionAuditMapTasteGate_single_carrier_alignment_injective heq
      · rfl

end BEDC.Derived.SubstitutionAuditMapUp
