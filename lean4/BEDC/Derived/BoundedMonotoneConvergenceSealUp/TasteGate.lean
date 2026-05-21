import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedMonotoneConvergenceSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedMonotoneConvergenceSealUp : Type where
  | mk
      (witness monotone criterion regular stream dyadic limitSeal realSeal transport route
        provenance name : BHist) :
      BoundedMonotoneConvergenceSealUp
  deriving DecidableEq

def boundedMonotoneConvergenceSealEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedMonotoneConvergenceSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedMonotoneConvergenceSealEncodeBHist h

def boundedMonotoneConvergenceSealDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedMonotoneConvergenceSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedMonotoneConvergenceSealDecodeBHist tail)

private theorem boundedMonotoneConvergenceSealDecode_encode_bhist :
    ∀ h : BHist,
      boundedMonotoneConvergenceSealDecodeBHist
        (boundedMonotoneConvergenceSealEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedMonotoneConvergenceSealToEventFlow :
    BoundedMonotoneConvergenceSealUp → EventFlow
  | BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regular stream dyadic
      limitSeal realSeal transport route provenance name =>
      [[BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist witness,
        [BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist monotone,
        [BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist criterion,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist regular,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist limitSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        boundedMonotoneConvergenceSealEncodeBHist name]

private def boundedMonotoneConvergenceSealDecodePacket
    (witness monotone criterion regular stream dyadic limitSeal realSeal transport route
      provenance name : RawEvent) :
    BoundedMonotoneConvergenceSealUp :=
  BoundedMonotoneConvergenceSealUp.mk
    (boundedMonotoneConvergenceSealDecodeBHist witness)
    (boundedMonotoneConvergenceSealDecodeBHist monotone)
    (boundedMonotoneConvergenceSealDecodeBHist criterion)
    (boundedMonotoneConvergenceSealDecodeBHist regular)
    (boundedMonotoneConvergenceSealDecodeBHist stream)
    (boundedMonotoneConvergenceSealDecodeBHist dyadic)
    (boundedMonotoneConvergenceSealDecodeBHist limitSeal)
    (boundedMonotoneConvergenceSealDecodeBHist realSeal)
    (boundedMonotoneConvergenceSealDecodeBHist transport)
    (boundedMonotoneConvergenceSealDecodeBHist route)
    (boundedMonotoneConvergenceSealDecodeBHist provenance)
    (boundedMonotoneConvergenceSealDecodeBHist name)

def boundedMonotoneConvergenceSealFromEventFlow :
    EventFlow → Option BoundedMonotoneConvergenceSealUp
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | witness :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | monotone :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | criterion :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | regular :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | stream :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | dyadic :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | limitSeal :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | realSeal :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | transport :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | route :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | provenance :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] => none
                                                                                          | _tag11 :: rest22 =>
                                                                                              match rest22 with
                                                                                              | [] => none
                                                                                              | name :: rest23 =>
                                                                                                  match rest23 with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (boundedMonotoneConvergenceSealDecodePacket
                                                                                                          witness
                                                                                                          monotone
                                                                                                          criterion
                                                                                                          regular
                                                                                                          stream
                                                                                                          dyadic
                                                                                                          limitSeal
                                                                                                          realSeal
                                                                                                          transport
                                                                                                          route
                                                                                                          provenance
                                                                                                          name)
                                                                                                  | _ :: _ => none

private theorem boundedMonotoneConvergenceSeal_round_trip :
    ∀ x : BoundedMonotoneConvergenceSealUp,
      boundedMonotoneConvergenceSealFromEventFlow
        (boundedMonotoneConvergenceSealToEventFlow x) = some x := by
  intro x
  cases x with
  | mk witness monotone criterion regular stream dyadic limitSeal realSeal transport route
      provenance name =>
      change
        some
            (boundedMonotoneConvergenceSealDecodePacket
              (boundedMonotoneConvergenceSealEncodeBHist witness)
              (boundedMonotoneConvergenceSealEncodeBHist monotone)
              (boundedMonotoneConvergenceSealEncodeBHist criterion)
              (boundedMonotoneConvergenceSealEncodeBHist regular)
              (boundedMonotoneConvergenceSealEncodeBHist stream)
              (boundedMonotoneConvergenceSealEncodeBHist dyadic)
              (boundedMonotoneConvergenceSealEncodeBHist limitSeal)
              (boundedMonotoneConvergenceSealEncodeBHist realSeal)
              (boundedMonotoneConvergenceSealEncodeBHist transport)
              (boundedMonotoneConvergenceSealEncodeBHist route)
              (boundedMonotoneConvergenceSealEncodeBHist provenance)
              (boundedMonotoneConvergenceSealEncodeBHist name)) =
          some
            (BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regular stream dyadic
              limitSeal realSeal transport route provenance name)
      unfold boundedMonotoneConvergenceSealDecodePacket
      rw [boundedMonotoneConvergenceSealDecode_encode_bhist witness,
        boundedMonotoneConvergenceSealDecode_encode_bhist monotone,
        boundedMonotoneConvergenceSealDecode_encode_bhist criterion,
        boundedMonotoneConvergenceSealDecode_encode_bhist regular,
        boundedMonotoneConvergenceSealDecode_encode_bhist stream,
        boundedMonotoneConvergenceSealDecode_encode_bhist dyadic,
        boundedMonotoneConvergenceSealDecode_encode_bhist limitSeal,
        boundedMonotoneConvergenceSealDecode_encode_bhist realSeal,
        boundedMonotoneConvergenceSealDecode_encode_bhist transport,
        boundedMonotoneConvergenceSealDecode_encode_bhist route,
        boundedMonotoneConvergenceSealDecode_encode_bhist provenance,
        boundedMonotoneConvergenceSealDecode_encode_bhist name]

private theorem boundedMonotoneConvergenceSealToEventFlow_injective
    {x y : BoundedMonotoneConvergenceSealUp} :
    boundedMonotoneConvergenceSealToEventFlow x =
      boundedMonotoneConvergenceSealToEventFlow y → x = y := by
  intro heq
  have hread :
      boundedMonotoneConvergenceSealFromEventFlow
          (boundedMonotoneConvergenceSealToEventFlow x) =
        boundedMonotoneConvergenceSealFromEventFlow
          (boundedMonotoneConvergenceSealToEventFlow y) :=
    congrArg boundedMonotoneConvergenceSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedMonotoneConvergenceSeal_round_trip x).symm
      (Eq.trans hread (boundedMonotoneConvergenceSeal_round_trip y)))

def boundedMonotoneConvergenceSealFields :
    BoundedMonotoneConvergenceSealUp → List BHist
  | BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regular stream dyadic
      limitSeal realSeal transport route provenance name =>
      [witness, monotone, criterion, regular, stream, dyadic, limitSeal, realSeal,
        transport, route, provenance, name]

private theorem boundedMonotoneConvergenceSeal_fields_faithful :
    ∀ x y : BoundedMonotoneConvergenceSealUp,
      boundedMonotoneConvergenceSealFields x =
        boundedMonotoneConvergenceSealFields y → x = y := by
  intro x y hfields
  cases x with
  | mk witness₁ monotone₁ criterion₁ regular₁ stream₁ dyadic₁ limitSeal₁ realSeal₁
      transport₁ route₁ provenance₁ name₁ =>
      cases y with
      | mk witness₂ monotone₂ criterion₂ regular₂ stream₂ dyadic₂ limitSeal₂ realSeal₂
          transport₂ route₂ provenance₂ name₂ =>
          injection hfields with hWitness tail0
          injection tail0 with hMonotone tail1
          injection tail1 with hCriterion tail2
          injection tail2 with hRegular tail3
          injection tail3 with hStream tail4
          injection tail4 with hDyadic tail5
          injection tail5 with hLimitSeal tail6
          injection tail6 with hRealSeal tail7
          injection tail7 with hTransport tail8
          injection tail8 with hRoute tail9
          injection tail9 with hProvenance tail10
          injection tail10 with hName _
          subst hWitness
          subst hMonotone
          subst hCriterion
          subst hRegular
          subst hStream
          subst hDyadic
          subst hLimitSeal
          subst hRealSeal
          subst hTransport
          subst hRoute
          subst hProvenance
          subst hName
          rfl

instance boundedMonotoneConvergenceSealBHistCarrier :
    BHistCarrier BoundedMonotoneConvergenceSealUp where
  toEventFlow := boundedMonotoneConvergenceSealToEventFlow
  fromEventFlow := boundedMonotoneConvergenceSealFromEventFlow

instance boundedMonotoneConvergenceSealChapterTasteGate :
    ChapterTasteGate BoundedMonotoneConvergenceSealUp where
  round_trip := by
    intro x
    change
      boundedMonotoneConvergenceSealFromEventFlow
        (boundedMonotoneConvergenceSealToEventFlow x) = some x
    exact boundedMonotoneConvergenceSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedMonotoneConvergenceSealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BoundedMonotoneConvergenceSealUp :=
  boundedMonotoneConvergenceSealChapterTasteGate

instance boundedMonotoneConvergenceSealFieldFaithful :
    FieldFaithful BoundedMonotoneConvergenceSealUp where
  fields := boundedMonotoneConvergenceSealFields
  field_faithful := boundedMonotoneConvergenceSeal_fields_faithful

instance boundedMonotoneConvergenceSealNontrivial :
    Nontrivial BoundedMonotoneConvergenceSealUp where
  witness_pair :=
    ⟨BoundedMonotoneConvergenceSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      BoundedMonotoneConvergenceSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem BoundedMonotoneConvergenceSealTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      boundedMonotoneConvergenceSealDecodeBHist
        (boundedMonotoneConvergenceSealEncodeBHist h) = h) ∧
      (∀ x : BoundedMonotoneConvergenceSealUp,
        boundedMonotoneConvergenceSealFromEventFlow
          (boundedMonotoneConvergenceSealToEventFlow x) = some x) ∧
        (∀ x y : BoundedMonotoneConvergenceSealUp,
          boundedMonotoneConvergenceSealToEventFlow x =
            boundedMonotoneConvergenceSealToEventFlow y → x = y) ∧
          boundedMonotoneConvergenceSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  constructor
  · exact boundedMonotoneConvergenceSealDecode_encode_bhist
  · constructor
    · exact boundedMonotoneConvergenceSeal_round_trip
    · constructor
      · intro x y heq
        exact boundedMonotoneConvergenceSealToEventFlow_injective heq
      · rfl

theorem BoundedMonotoneConvergenceSealUp_witness_consumption
    {witness monotone criterion regular stream dyadic limitSeal realSeal transport route
      provenance name witness' monotone' criterion' regular' stream' dyadic' limitSeal'
      realSeal' transport' route' provenance' name' : BHist} :
    FieldFaithful.fields
        (BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regular stream dyadic
          limitSeal realSeal transport route provenance name) =
      FieldFaithful.fields
        (BoundedMonotoneConvergenceSealUp.mk witness' monotone' criterion' regular' stream'
          dyadic' limitSeal' realSeal' transport' route' provenance' name') →
      Cont witness monotone route →
        Cont witness' monotone' route' →
          witness = witness' ∧ monotone = monotone' ∧ route = route' := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  intro hfields _route _route'
  change
      boundedMonotoneConvergenceSealFields
          (BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regular stream
            dyadic limitSeal realSeal transport route provenance name) =
        boundedMonotoneConvergenceSealFields
          (BoundedMonotoneConvergenceSealUp.mk witness' monotone' criterion' regular'
            stream' dyadic' limitSeal' realSeal' transport' route' provenance' name') at hfields
  injection hfields with hWitness tail0
  injection tail0 with hMonotone tail1
  injection tail1 with _hCriterion tail2
  injection tail2 with _hRegular tail3
  injection tail3 with _hStream tail4
  injection tail4 with _hDyadic tail5
  injection tail5 with _hLimitSeal tail6
  injection tail6 with _hRealSeal tail7
  injection tail7 with _hTransport tail8
  injection tail8 with hRoute _tail9
  exact ⟨hWitness, hMonotone, hRoute⟩

theorem BoundedMonotoneConvergenceSealUp_criterion_route
    {witness monotone criterion regular stream dyadic limitSeal realSeal transport route
      provenance name witness' monotone' criterion' regular' stream' dyadic' limitSeal'
      realSeal' transport' route' provenance' name' : BHist} :
    FieldFaithful.fields
        (BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regular stream dyadic
          limitSeal realSeal transport route provenance name) =
      FieldFaithful.fields
        (BoundedMonotoneConvergenceSealUp.mk witness' monotone' criterion' regular' stream'
          dyadic' limitSeal' realSeal' transport' route' provenance' name') →
      Cont monotone criterion route →
        Cont monotone' criterion' route' →
          monotone = monotone' ∧ criterion = criterion' ∧ regular = regular' ∧
            stream = stream' ∧ dyadic = dyadic' ∧ limitSeal = limitSeal' ∧
              Cont monotone criterion route ∧ Cont monotone' criterion' route' := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  intro hfields routeCont routeCont'
  change
      boundedMonotoneConvergenceSealFields
          (BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regular stream
            dyadic limitSeal realSeal transport route provenance name) =
        boundedMonotoneConvergenceSealFields
          (BoundedMonotoneConvergenceSealUp.mk witness' monotone' criterion' regular'
            stream' dyadic' limitSeal' realSeal' transport' route' provenance' name') at hfields
  injection hfields with _hWitness tail0
  injection tail0 with hMonotone tail1
  injection tail1 with hCriterion tail2
  injection tail2 with hRegular tail3
  injection tail3 with hStream tail4
  injection tail4 with hDyadic tail5
  injection tail5 with hLimitSeal _tail6
  exact
    ⟨hMonotone, hCriterion, hRegular, hStream, hDyadic, hLimitSeal, routeCont,
      routeCont'⟩

theorem BoundedMonotoneConvergenceSealUp_real_handoff
    {witness monotone criterion regular stream dyadic limitSeal realSeal transport route
      provenance name witness' monotone' criterion' regular' stream' dyadic' limitSeal'
      realSeal' transport' route' provenance' name' terminal terminal' : BHist} :
    FieldFaithful.fields
        (BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regular stream dyadic
          limitSeal realSeal transport route provenance name) =
      FieldFaithful.fields
        (BoundedMonotoneConvergenceSealUp.mk witness' monotone' criterion' regular' stream'
          dyadic' limitSeal' realSeal' transport' route' provenance' name') →
      Cont dyadic limitSeal realSeal →
        Cont realSeal route terminal →
          Cont dyadic' limitSeal' realSeal' →
            Cont realSeal' route' terminal' →
              realSeal = realSeal' ∧ route = route' ∧ Cont dyadic limitSeal realSeal ∧
                Cont realSeal route terminal ∧ Cont dyadic' limitSeal' realSeal' ∧
                  Cont realSeal' route' terminal' := by
  -- BEDC touchpoint anchor: BHist Cont FieldFaithful
  intro hfields dyadicLimitSeal realRoute dyadicLimitSeal' realRoute'
  change
      boundedMonotoneConvergenceSealFields
          (BoundedMonotoneConvergenceSealUp.mk witness monotone criterion regular stream
            dyadic limitSeal realSeal transport route provenance name) =
        boundedMonotoneConvergenceSealFields
          (BoundedMonotoneConvergenceSealUp.mk witness' monotone' criterion' regular'
            stream' dyadic' limitSeal' realSeal' transport' route' provenance' name') at hfields
  injection hfields with _hWitness tail0
  injection tail0 with _hMonotone tail1
  injection tail1 with _hCriterion tail2
  injection tail2 with _hRegular tail3
  injection tail3 with _hStream tail4
  injection tail4 with _hDyadic tail5
  injection tail5 with _hLimitSeal tail6
  injection tail6 with hRealSeal tail7
  injection tail7 with _hTransport tail8
  injection tail8 with hRoute _tail9
  exact
    ⟨hRealSeal, hRoute, dyadicLimitSeal, realRoute, dyadicLimitSeal',
      realRoute'⟩

end BEDC.Derived.BoundedMonotoneConvergenceSealUp
