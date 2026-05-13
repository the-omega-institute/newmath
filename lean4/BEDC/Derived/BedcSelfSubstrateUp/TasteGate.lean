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
  | [_, generators, _, equality, _, recursors, _, purity, _, boundary, _, transport, _, route, _,
      provenance, _, name] =>
      some
        (BedcSelfSubstrateUp.mk
          (bedcSelfSubstrateDecodeBHist generators)
          (bedcSelfSubstrateDecodeBHist equality)
          (bedcSelfSubstrateDecodeBHist recursors)
          (bedcSelfSubstrateDecodeBHist purity)
          (bedcSelfSubstrateDecodeBHist boundary)
          (bedcSelfSubstrateDecodeBHist transport)
          (bedcSelfSubstrateDecodeBHist route)
          (bedcSelfSubstrateDecodeBHist provenance)
          (bedcSelfSubstrateDecodeBHist name))
  | _ => none

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
            injection hfields with hGenerators hTail0
            injection hTail0 with hEquality hTail1
            injection hTail1 with hRecursors hTail2
            injection hTail2 with hPurity hTail3
            injection hTail3 with hBoundary hTail4
            injection hTail4 with hTransport hTail5
            injection hTail5 with hRoute hTail6
            injection hTail6 with hProvenance hTail7
            injection hTail7 with hName _hNil
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

theorem BedcSelfSubstrateTasteGate_single_carrier_alignment :
    (∀ h : BHist, bedcSelfSubstrateDecodeBHist (bedcSelfSubstrateEncodeBHist h) = h) ∧
      (∀ x y : BedcSelfSubstrateUp,
        bedcSelfSubstrateToEventFlow x = bedcSelfSubstrateToEventFlow y → x = y) ∧
        (∀ x y : BedcSelfSubstrateUp,
          (match x with
            | BedcSelfSubstrateUp.mk generators equality recursors purity boundary transport
                route provenance name =>
                [generators, equality, recursors, purity, boundary, transport, route,
                  provenance, name]) =
            (match y with
              | BedcSelfSubstrateUp.mk generators equality recursors purity boundary transport
                  route provenance name =>
                  [generators, equality, recursors, purity, boundary, transport, route,
                    provenance, name]) →
            x = y) ∧
          (∃ x y : BedcSelfSubstrateUp, x ≠ y) := by
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro x y heq
      cases x with
      | mk generators equality recursors purity boundary transport route provenance name =>
          cases y with
          | mk generators' equality' recursors' purity' boundary' transport' route'
              provenance' name' =>
              injection heq with _ hTail0
              injection hTail0 with hGenerators hTail1
              injection hTail1 with _ hTail2
              injection hTail2 with hEquality hTail3
              injection hTail3 with _ hTail4
              injection hTail4 with hRecursors hTail5
              injection hTail5 with _ hTail6
              injection hTail6 with hPurity hTail7
              injection hTail7 with _ hTail8
              injection hTail8 with hBoundary hTail9
              injection hTail9 with _ hTail10
              injection hTail10 with hTransport hTail11
              injection hTail11 with _ hTail12
              injection hTail12 with hRoute hTail13
              injection hTail13 with _ hTail14
              injection hTail14 with hProvenance hTail15
              injection hTail15 with _ hTail16
              injection hTail16 with hName _hNil
              have sameGenerators : generators = generators' := by
                have hDecoded := congrArg bedcSelfSubstrateDecodeBHist hGenerators
                exact Eq.trans (bedcSelfSubstrateDecode_encode_bhist generators).symm
                  (Eq.trans hDecoded (bedcSelfSubstrateDecode_encode_bhist generators'))
              have sameEquality : equality = equality' := by
                have hDecoded := congrArg bedcSelfSubstrateDecodeBHist hEquality
                exact Eq.trans (bedcSelfSubstrateDecode_encode_bhist equality).symm
                  (Eq.trans hDecoded (bedcSelfSubstrateDecode_encode_bhist equality'))
              have sameRecursors : recursors = recursors' := by
                have hDecoded := congrArg bedcSelfSubstrateDecodeBHist hRecursors
                exact Eq.trans (bedcSelfSubstrateDecode_encode_bhist recursors).symm
                  (Eq.trans hDecoded (bedcSelfSubstrateDecode_encode_bhist recursors'))
              have samePurity : purity = purity' := by
                have hDecoded := congrArg bedcSelfSubstrateDecodeBHist hPurity
                exact Eq.trans (bedcSelfSubstrateDecode_encode_bhist purity).symm
                  (Eq.trans hDecoded (bedcSelfSubstrateDecode_encode_bhist purity'))
              have sameBoundary : boundary = boundary' := by
                have hDecoded := congrArg bedcSelfSubstrateDecodeBHist hBoundary
                exact Eq.trans (bedcSelfSubstrateDecode_encode_bhist boundary).symm
                  (Eq.trans hDecoded (bedcSelfSubstrateDecode_encode_bhist boundary'))
              have sameTransport : transport = transport' := by
                have hDecoded := congrArg bedcSelfSubstrateDecodeBHist hTransport
                exact Eq.trans (bedcSelfSubstrateDecode_encode_bhist transport).symm
                  (Eq.trans hDecoded (bedcSelfSubstrateDecode_encode_bhist transport'))
              have sameRoute : route = route' := by
                have hDecoded := congrArg bedcSelfSubstrateDecodeBHist hRoute
                exact Eq.trans (bedcSelfSubstrateDecode_encode_bhist route).symm
                  (Eq.trans hDecoded (bedcSelfSubstrateDecode_encode_bhist route'))
              have sameProvenance : provenance = provenance' := by
                have hDecoded := congrArg bedcSelfSubstrateDecodeBHist hProvenance
                exact Eq.trans (bedcSelfSubstrateDecode_encode_bhist provenance).symm
                  (Eq.trans hDecoded (bedcSelfSubstrateDecode_encode_bhist provenance'))
              have sameName : name = name' := by
                have hDecoded := congrArg bedcSelfSubstrateDecodeBHist hName
                exact Eq.trans (bedcSelfSubstrateDecode_encode_bhist name).symm
                  (Eq.trans hDecoded (bedcSelfSubstrateDecode_encode_bhist name'))
              cases sameGenerators
              cases sameEquality
              cases sameRecursors
              cases samePurity
              cases sameBoundary
              cases sameTransport
              cases sameRoute
              cases sameProvenance
              cases sameName
              rfl
    · constructor
      · intro x y hfields
        cases x with
        | mk generators equality recursors purity boundary transport route provenance name =>
            cases y with
            | mk generators' equality' recursors' purity' boundary' transport' route'
                provenance' name' =>
                change
                  [generators, equality, recursors, purity, boundary, transport, route,
                      provenance, name] =
                    [generators', equality', recursors', purity', boundary', transport',
                      route', provenance', name'] at hfields
                injection hfields with hGenerators hTail0
                injection hTail0 with hEquality hTail1
                injection hTail1 with hRecursors hTail2
                injection hTail2 with hPurity hTail3
                injection hTail3 with hBoundary hTail4
                injection hTail4 with hTransport hTail5
                injection hTail5 with hRoute hTail6
                injection hTail6 with hProvenance hTail7
                injection hTail7 with hName _hNil
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
      · exact
          ⟨BedcSelfSubstrateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            BedcSelfSubstrateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
            by
              intro h
              cases h⟩

end BEDC.Derived.BedcSelfSubstrateUp
