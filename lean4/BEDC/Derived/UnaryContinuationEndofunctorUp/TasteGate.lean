import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.UnaryContinuationEndofunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive UnaryContinuationEndofunctorUp : Type where
  | mk :
      (object hom action identity composition transport route provenance localName : BHist) →
      UnaryContinuationEndofunctorUp
  deriving DecidableEq

def unaryContinuationEndofunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: unaryContinuationEndofunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: unaryContinuationEndofunctorEncodeBHist h

def unaryContinuationEndofunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (unaryContinuationEndofunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (unaryContinuationEndofunctorDecodeBHist tail)

private theorem unaryContinuationEndofunctor_decode_encode_bhist :
    ∀ h : BHist,
      unaryContinuationEndofunctorDecodeBHist
        (unaryContinuationEndofunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem unaryContinuationEndofunctor_encode_bhist_injective
    {h k : BHist} :
    unaryContinuationEndofunctorEncodeBHist h =
      unaryContinuationEndofunctorEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hdecode :
      unaryContinuationEndofunctorDecodeBHist
          (unaryContinuationEndofunctorEncodeBHist h) =
        unaryContinuationEndofunctorDecodeBHist
          (unaryContinuationEndofunctorEncodeBHist k) :=
    congrArg unaryContinuationEndofunctorDecodeBHist heq
  exact
    Eq.trans (unaryContinuationEndofunctor_decode_encode_bhist h).symm
      (Eq.trans hdecode (unaryContinuationEndofunctor_decode_encode_bhist k))

def unaryContinuationEndofunctorFields :
    UnaryContinuationEndofunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | UnaryContinuationEndofunctorUp.mk object hom action identity composition transport
      route provenance localName =>
      [object, hom, action, identity, composition, transport, route, provenance, localName]

def unaryContinuationEndofunctorToEventFlow :
    UnaryContinuationEndofunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (unaryContinuationEndofunctorFields x).map
      unaryContinuationEndofunctorEncodeBHist

def unaryContinuationEndofunctorFromEventFlow :
    EventFlow → Option UnaryContinuationEndofunctorUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | object :: rest0 =>
      match rest0 with
      | [] => none
      | hom :: rest1 =>
          match rest1 with
          | [] => none
          | action :: rest2 =>
              match rest2 with
              | [] => none
              | identity :: rest3 =>
                  match rest3 with
                  | [] => none
                  | composition :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | localName :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (UnaryContinuationEndofunctorUp.mk
                                              (unaryContinuationEndofunctorDecodeBHist object)
                                              (unaryContinuationEndofunctorDecodeBHist hom)
                                              (unaryContinuationEndofunctorDecodeBHist action)
                                              (unaryContinuationEndofunctorDecodeBHist
                                                identity)
                                              (unaryContinuationEndofunctorDecodeBHist
                                                composition)
                                              (unaryContinuationEndofunctorDecodeBHist
                                                transport)
                                              (unaryContinuationEndofunctorDecodeBHist route)
                                              (unaryContinuationEndofunctorDecodeBHist
                                                provenance)
                                              (unaryContinuationEndofunctorDecodeBHist
                                                localName))
                                      | _extra :: _rest => none

private theorem unaryContinuationEndofunctor_round_trip :
    ∀ x : UnaryContinuationEndofunctorUp,
      unaryContinuationEndofunctorFromEventFlow
        (unaryContinuationEndofunctorToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk object hom action identity composition transport route provenance localName =>
      change
        some
          (UnaryContinuationEndofunctorUp.mk
            (unaryContinuationEndofunctorDecodeBHist
              (unaryContinuationEndofunctorEncodeBHist object))
            (unaryContinuationEndofunctorDecodeBHist
              (unaryContinuationEndofunctorEncodeBHist hom))
            (unaryContinuationEndofunctorDecodeBHist
              (unaryContinuationEndofunctorEncodeBHist action))
            (unaryContinuationEndofunctorDecodeBHist
              (unaryContinuationEndofunctorEncodeBHist identity))
            (unaryContinuationEndofunctorDecodeBHist
              (unaryContinuationEndofunctorEncodeBHist composition))
            (unaryContinuationEndofunctorDecodeBHist
              (unaryContinuationEndofunctorEncodeBHist transport))
            (unaryContinuationEndofunctorDecodeBHist
              (unaryContinuationEndofunctorEncodeBHist route))
            (unaryContinuationEndofunctorDecodeBHist
              (unaryContinuationEndofunctorEncodeBHist provenance))
            (unaryContinuationEndofunctorDecodeBHist
              (unaryContinuationEndofunctorEncodeBHist localName))) =
          some
            (UnaryContinuationEndofunctorUp.mk object hom action identity composition
              transport route provenance localName)
      rw [unaryContinuationEndofunctor_decode_encode_bhist object,
        unaryContinuationEndofunctor_decode_encode_bhist hom,
        unaryContinuationEndofunctor_decode_encode_bhist action,
        unaryContinuationEndofunctor_decode_encode_bhist identity,
        unaryContinuationEndofunctor_decode_encode_bhist composition,
        unaryContinuationEndofunctor_decode_encode_bhist transport,
        unaryContinuationEndofunctor_decode_encode_bhist route,
        unaryContinuationEndofunctor_decode_encode_bhist provenance,
        unaryContinuationEndofunctor_decode_encode_bhist localName]

private theorem unaryContinuationEndofunctorToEventFlow_injective
    {x y : UnaryContinuationEndofunctorUp} :
    unaryContinuationEndofunctorToEventFlow x =
      unaryContinuationEndofunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk object hom action identity composition transport route provenance localName =>
      cases y with
      | mk object' hom' action' identity' composition' transport' route' provenance'
          localName' =>
          injection heq with hobject tailObject
          injection tailObject with hhom tailHom
          injection tailHom with haction tailAction
          injection tailAction with hidentity tailIdentity
          injection tailIdentity with hcomposition tailComposition
          injection tailComposition with htransport tailTransport
          injection tailTransport with hroute tailRoute
          injection tailRoute with hprovenance tailProvenance
          injection tailProvenance with hlocalName _
          have objectEq : object = object' :=
            unaryContinuationEndofunctor_encode_bhist_injective hobject
          have homEq : hom = hom' :=
            unaryContinuationEndofunctor_encode_bhist_injective hhom
          have actionEq : action = action' :=
            unaryContinuationEndofunctor_encode_bhist_injective haction
          have identityEq : identity = identity' :=
            unaryContinuationEndofunctor_encode_bhist_injective hidentity
          have compositionEq : composition = composition' :=
            unaryContinuationEndofunctor_encode_bhist_injective hcomposition
          have transportEq : transport = transport' :=
            unaryContinuationEndofunctor_encode_bhist_injective htransport
          have routeEq : route = route' :=
            unaryContinuationEndofunctor_encode_bhist_injective hroute
          have provenanceEq : provenance = provenance' :=
            unaryContinuationEndofunctor_encode_bhist_injective hprovenance
          have localNameEq : localName = localName' :=
            unaryContinuationEndofunctor_encode_bhist_injective hlocalName
          cases objectEq
          cases homEq
          cases actionEq
          cases identityEq
          cases compositionEq
          cases transportEq
          cases routeEq
          cases provenanceEq
          cases localNameEq
          rfl

instance unaryContinuationEndofunctorBHistCarrier :
    BHistCarrier UnaryContinuationEndofunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := unaryContinuationEndofunctorToEventFlow
  fromEventFlow := unaryContinuationEndofunctorFromEventFlow

instance unaryContinuationEndofunctorChapterTasteGate :
    ChapterTasteGate UnaryContinuationEndofunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      unaryContinuationEndofunctorFromEventFlow
        (unaryContinuationEndofunctorToEventFlow x) = some x
    exact unaryContinuationEndofunctor_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (unaryContinuationEndofunctorToEventFlow_injective heq)

def taste_gate : ChapterTasteGate UnaryContinuationEndofunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  unaryContinuationEndofunctorChapterTasteGate

theorem UnaryContinuationEndofunctorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      unaryContinuationEndofunctorDecodeBHist
        (unaryContinuationEndofunctorEncodeBHist h) = h) ∧
      (∀ x : UnaryContinuationEndofunctorUp,
        unaryContinuationEndofunctorFromEventFlow
          (unaryContinuationEndofunctorToEventFlow x) = some x) ∧
        (∀ x y : UnaryContinuationEndofunctorUp,
          unaryContinuationEndofunctorToEventFlow x =
            unaryContinuationEndofunctorToEventFlow y → x = y) ∧
          unaryContinuationEndofunctorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨unaryContinuationEndofunctor_decode_encode_bhist,
      unaryContinuationEndofunctor_round_trip,
      (fun _ _ heq => unaryContinuationEndofunctorToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.UnaryContinuationEndofunctorUp
