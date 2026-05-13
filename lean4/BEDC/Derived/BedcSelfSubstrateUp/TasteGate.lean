import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BedcSelfSubstrateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BedcSelfSubstrateUp : Type where
  | mk : (generators equality recursors purity boundary transport route provenance name : BHist) →
      BedcSelfSubstrateUp
  deriving DecidableEq

def bedcSelfSubstrateEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bedcSelfSubstrateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bedcSelfSubstrateEncodeBHist h

def bedcSelfSubstrateDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bedcSelfSubstrateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bedcSelfSubstrateDecodeBHist tail)

private theorem bedcSelfSubstrateDecode_encode_bhist :
    ∀ h : BHist, bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem bedcSelfSubstrate_mk_congr
    {generators generators' equality equality' recursors recursors' purity purity' boundary
      boundary' transport transport' route route' provenance provenance' name name' : BHist}
    (hGenerators : generators' = generators)
    (hEquality : equality' = equality)
    (hRecursors : recursors' = recursors)
    (hPurity : purity' = purity)
    (hBoundary : boundary' = boundary)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    BedcSelfSubstrateUp.mk generators' equality' recursors' purity' boundary' transport' route'
        provenance' name' =
      BedcSelfSubstrateUp.mk generators equality recursors purity boundary transport route
        provenance name := by
  cases hGenerators
  cases hEquality
  cases hRecursors
  cases hPurity
  cases hBoundary
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def bedcSelfSubstrateToEventFlow : BedcSelfSubstrateUp → EventFlow
  | BedcSelfSubstrateUp.mk generators equality recursors purity boundary transport route provenance
      name =>
      [[BMark.b0],
        bedcSelfSubstrateEncodeBHist generators,
        [BMark.b1, BMark.b0],
        bedcSelfSubstrateEncodeBHist equality,
        [BMark.b1, BMark.b1, BMark.b0],
        bedcSelfSubstrateEncodeBHist recursors,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcSelfSubstrateEncodeBHist purity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcSelfSubstrateEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcSelfSubstrateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcSelfSubstrateEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bedcSelfSubstrateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bedcSelfSubstrateEncodeBHist name]

def bedcSelfSubstrateFromEventFlow : EventFlow → Option BedcSelfSubstrateUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | generators :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | equality :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | recursors :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | purity :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | boundary :: rest9 =>
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
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | name :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (BedcSelfSubstrateUp.mk
                                                                                  (bedcSelfSubstrateDecodeBHist
                                                                                    generators)
                                                                                  (bedcSelfSubstrateDecodeBHist
                                                                                    equality)
                                                                                  (bedcSelfSubstrateDecodeBHist
                                                                                    recursors)
                                                                                  (bedcSelfSubstrateDecodeBHist
                                                                                    purity)
                                                                                  (bedcSelfSubstrateDecodeBHist
                                                                                    boundary)
                                                                                  (bedcSelfSubstrateDecodeBHist
                                                                                    transport)
                                                                                  (bedcSelfSubstrateDecodeBHist
                                                                                    route)
                                                                                  (bedcSelfSubstrateDecodeBHist
                                                                                    provenance)
                                                                                  (bedcSelfSubstrateDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem bedcSelfSubstrate_round_trip :
    ∀ x : BedcSelfSubstrateUp,
      bedcSelfSubstrateFromEventFlow (bedcSelfSubstrateToEventFlow x) = some x := by
  intro x
  cases x with
  | mk generators equality recursors purity boundary transport route provenance name =>
      change
        some
          (BedcSelfSubstrateUp.mk
            (bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist generators))
            (bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist equality))
            (bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist recursors))
            (bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist purity))
            (bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist boundary))
            (bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist transport))
            (bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist route))
            (bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist provenance))
            (bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist name))) =
          some
            (BedcSelfSubstrateUp.mk generators equality recursors purity boundary transport route
              provenance name)
      exact
        congrArg some
          (bedcSelfSubstrate_mk_congr
            (bedcSelfSubstrateDecode_encode_bhist generators)
            (bedcSelfSubstrateDecode_encode_bhist equality)
            (bedcSelfSubstrateDecode_encode_bhist recursors)
            (bedcSelfSubstrateDecode_encode_bhist purity)
            (bedcSelfSubstrateDecode_encode_bhist boundary)
            (bedcSelfSubstrateDecode_encode_bhist transport)
            (bedcSelfSubstrateDecode_encode_bhist route)
            (bedcSelfSubstrateDecode_encode_bhist provenance)
            (bedcSelfSubstrateDecode_encode_bhist name))

private theorem bedcSelfSubstrateToEventFlow_injective {x y : BedcSelfSubstrateUp} :
    bedcSelfSubstrateToEventFlow x = bedcSelfSubstrateToEventFlow y → x = y := by
  intro heq
  have hread :
      bedcSelfSubstrateFromEventFlow (bedcSelfSubstrateToEventFlow x) =
        bedcSelfSubstrateFromEventFlow (bedcSelfSubstrateToEventFlow y) :=
    congrArg bedcSelfSubstrateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bedcSelfSubstrate_round_trip x).symm
      (Eq.trans hread (bedcSelfSubstrate_round_trip y)))

instance bedcSelfSubstrateBHistCarrier : BHistCarrier BedcSelfSubstrateUp where
  toEventFlow := bedcSelfSubstrateToEventFlow
  fromEventFlow := bedcSelfSubstrateFromEventFlow

instance bedcSelfSubstrateChapterTasteGate : ChapterTasteGate BedcSelfSubstrateUp where
  round_trip := by
    intro x
    change bedcSelfSubstrateFromEventFlow (bedcSelfSubstrateToEventFlow x) = some x
    exact bedcSelfSubstrate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bedcSelfSubstrateToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BedcSelfSubstrateUp :=
  bedcSelfSubstrateChapterTasteGate

instance bedcSelfSubstrateNontrivial : Nontrivial BedcSelfSubstrateUp where
  witness_pair :=
    ⟨BedcSelfSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BedcSelfSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance bedcSelfSubstrateFieldFaithful : FieldFaithful BedcSelfSubstrateUp where
  fields
    | BedcSelfSubstrateUp.mk generators equality recursors purity boundary transport route
        provenance name =>
        [generators, equality, recursors, purity, boundary, transport, route, provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk generators equality recursors purity boundary transport route provenance name =>
        cases y with
        | mk generators' equality' recursors' purity' boundary' transport' route' provenance'
            name' =>
            cases hfields
            rfl

theorem BedcSelfSubstrateTasteGate_single_carrier_alignment :
    (∀ h : BHist, bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist h) = h) ∧
      (∀ x : BedcSelfSubstrateUp,
        bedcSelfSubstrateFromEventFlow (bedcSelfSubstrateToEventFlow x) = some x) ∧
        (∀ x y : BedcSelfSubstrateUp,
          bedcSelfSubstrateToEventFlow x = bedcSelfSubstrateToEventFlow y → x = y) ∧
          bedcSelfSubstrateEncodeBHist BHist.Empty = ([] : List BMark) := by
  constructor
  · exact bedcSelfSubstrateDecode_encode_bhist
  · constructor
    · exact bedcSelfSubstrate_round_trip
    · constructor
      · intro x y heq
        exact bedcSelfSubstrateToEventFlow_injective heq
      · rfl

end BEDC.Derived.BedcSelfSubstrateUp
