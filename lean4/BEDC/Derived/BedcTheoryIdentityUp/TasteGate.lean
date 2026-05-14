import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BedcTheoryIdentityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BedcTheoryIdentityUp : Type where
  | mk :
      (generators equality recursors purity boundary transport route provenance name : BHist) →
        BedcTheoryIdentityUp
  deriving DecidableEq

private def bedcTheoryIdentityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bedcTheoryIdentityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bedcTheoryIdentityEncodeBHist h

private def bedcTheoryIdentityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bedcTheoryIdentityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bedcTheoryIdentityDecodeBHist tail)

private theorem bedcTheoryIdentityDecodeEncodeBHist :
    ∀ h : BHist,
      bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem bedcTheoryIdentity_mk_congr
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
    BedcTheoryIdentityUp.mk generators' equality' recursors' purity' boundary' transport' route'
        provenance' name' =
      BedcTheoryIdentityUp.mk generators equality recursors purity boundary transport route
        provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
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

private def bedcTheoryIdentityToEventFlow : BedcTheoryIdentityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | BedcTheoryIdentityUp.mk generators equality recursors purity boundary transport route
      provenance name =>
      [[BMark.b0],
        bedcTheoryIdentityEncodeBHist generators,
        [BMark.b1, BMark.b0],
        bedcTheoryIdentityEncodeBHist equality,
        [BMark.b1, BMark.b1, BMark.b0],
        bedcTheoryIdentityEncodeBHist recursors,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcTheoryIdentityEncodeBHist purity,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcTheoryIdentityEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcTheoryIdentityEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        bedcTheoryIdentityEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        bedcTheoryIdentityEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        bedcTheoryIdentityEncodeBHist name]

private def bedcTheoryIdentityFromEventFlow :
    EventFlow → Option BedcTheoryIdentityUp
  -- BEDC touchpoint anchor: BHist BMark
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
                                                                                (BedcTheoryIdentityUp.mk
                                                                                  (bedcTheoryIdentityDecodeBHist
                                                                                    generators)
                                                                                  (bedcTheoryIdentityDecodeBHist
                                                                                    equality)
                                                                                  (bedcTheoryIdentityDecodeBHist
                                                                                    recursors)
                                                                                  (bedcTheoryIdentityDecodeBHist
                                                                                    purity)
                                                                                  (bedcTheoryIdentityDecodeBHist
                                                                                    boundary)
                                                                                  (bedcTheoryIdentityDecodeBHist
                                                                                    transport)
                                                                                  (bedcTheoryIdentityDecodeBHist
                                                                                    route)
                                                                                  (bedcTheoryIdentityDecodeBHist
                                                                                    provenance)
                                                                                  (bedcTheoryIdentityDecodeBHist
                                                                                    name))
                                                                          | _ :: _ => none

private theorem bedcTheoryIdentityRoundTrip :
    ∀ x : BedcTheoryIdentityUp,
      bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk generators equality recursors purity boundary transport route provenance name =>
      change
        some
          (BedcTheoryIdentityUp.mk
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist generators))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist equality))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist recursors))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist purity))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist boundary))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist transport))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist route))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist provenance))
            (bedcTheoryIdentityDecodeBHist (bedcTheoryIdentityEncodeBHist name))) =
          some
            (BedcTheoryIdentityUp.mk generators equality recursors purity boundary transport
              route provenance name)
      exact
        congrArg some
          (bedcTheoryIdentity_mk_congr
            (bedcTheoryIdentityDecodeEncodeBHist generators)
            (bedcTheoryIdentityDecodeEncodeBHist equality)
            (bedcTheoryIdentityDecodeEncodeBHist recursors)
            (bedcTheoryIdentityDecodeEncodeBHist purity)
            (bedcTheoryIdentityDecodeEncodeBHist boundary)
            (bedcTheoryIdentityDecodeEncodeBHist transport)
            (bedcTheoryIdentityDecodeEncodeBHist route)
            (bedcTheoryIdentityDecodeEncodeBHist provenance)
            (bedcTheoryIdentityDecodeEncodeBHist name))

private theorem bedcTheoryIdentityToEventFlow_injective
    {x y : BedcTheoryIdentityUp} :
    bedcTheoryIdentityToEventFlow x = bedcTheoryIdentityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow x) =
        bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow y) :=
    congrArg bedcTheoryIdentityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bedcTheoryIdentityRoundTrip x).symm
      (Eq.trans hread (bedcTheoryIdentityRoundTrip y)))

private def bedcTheoryIdentityFields : BedcTheoryIdentityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BedcTheoryIdentityUp.mk generators equality recursors purity boundary transport route
      provenance name =>
      [generators, equality, recursors, purity, boundary, transport, route, provenance, name]

private theorem bedcTheoryIdentity_field_faithful :
    ∀ x y : BedcTheoryIdentityUp,
      bedcTheoryIdentityFields x = bedcTheoryIdentityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk generators equality recursors purity boundary transport route provenance name =>
      cases y with
      | mk generators' equality' recursors' purity' boundary' transport' route' provenance'
          name' =>
          cases hfields
          rfl

instance bedcTheoryIdentityBHistCarrier : BHistCarrier BedcTheoryIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bedcTheoryIdentityToEventFlow
  fromEventFlow := bedcTheoryIdentityFromEventFlow

instance bedcTheoryIdentityChapterTasteGate : ChapterTasteGate BedcTheoryIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow x) = some x
    exact bedcTheoryIdentityRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bedcTheoryIdentityToEventFlow_injective heq)

instance bedcTheoryIdentityFieldFaithful : FieldFaithful BedcTheoryIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bedcTheoryIdentityFields
  field_faithful := bedcTheoryIdentity_field_faithful

instance bedcTheoryIdentityNontrivial : Nontrivial BedcTheoryIdentityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BedcTheoryIdentityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BedcTheoryIdentityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BedcTheoryIdentityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bedcTheoryIdentityChapterTasteGate

theorem BedcTheoryIdentityTasteGate_single_carrier_alignment :
    (∀ h : BHist, bedcTheoryIdentityDecodeBHist
        (bedcTheoryIdentityEncodeBHist h) = h) ∧
      (∀ x : BedcTheoryIdentityUp,
        bedcTheoryIdentityFromEventFlow (bedcTheoryIdentityToEventFlow x) = some x) ∧
        (∀ x y : BedcTheoryIdentityUp,
          bedcTheoryIdentityToEventFlow x = bedcTheoryIdentityToEventFlow y → x = y) ∧
          bedcTheoryIdentityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact bedcTheoryIdentityDecodeEncodeBHist
  · constructor
    · exact bedcTheoryIdentityRoundTrip
    · constructor
      · intro x y heq
        exact bedcTheoryIdentityToEventFlow_injective heq
      · rfl

end BEDC.Derived.BedcTheoryIdentityUp
