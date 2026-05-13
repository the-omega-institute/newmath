import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PrefixObserverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PrefixObserverUp : Type where
  | mk :
      (source prefixRow route check consumer ledger transport routes provenance nameCert : BHist) →
      PrefixObserverUp
  deriving DecidableEq

def prefixObserverEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: prefixObserverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: prefixObserverEncodeBHist h

def prefixObserverDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (prefixObserverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (prefixObserverDecodeBHist tail)

private theorem prefixObserverDecode_encode_bhist :
    ∀ h : BHist, prefixObserverDecodeBHist (prefixObserverEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def prefixObserverToEventFlow : PrefixObserverUp → EventFlow
  | PrefixObserverUp.mk source prefixRow route check consumer ledger transport routes provenance
      nameCert =>
      [[BMark.b0],
        prefixObserverEncodeBHist source,
        [BMark.b1, BMark.b0],
        prefixObserverEncodeBHist prefixRow,
        [BMark.b1, BMark.b1, BMark.b0],
        prefixObserverEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prefixObserverEncodeBHist check,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prefixObserverEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prefixObserverEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        prefixObserverEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        prefixObserverEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        prefixObserverEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        prefixObserverEncodeBHist nameCert]

def prefixObserverFromEventFlow : EventFlow → Option PrefixObserverUp
  | [_tag0, source, _tag1, prefixRow, _tag2, route, _tag3, check, _tag4, consumer,
      _tag5, ledger, _tag6, transport, _tag7, routes, _tag8, provenance, _tag9,
      nameCert] =>
      some
        (PrefixObserverUp.mk
          (prefixObserverDecodeBHist source)
          (prefixObserverDecodeBHist prefixRow)
          (prefixObserverDecodeBHist route)
          (prefixObserverDecodeBHist check)
          (prefixObserverDecodeBHist consumer)
          (prefixObserverDecodeBHist ledger)
          (prefixObserverDecodeBHist transport)
          (prefixObserverDecodeBHist routes)
          (prefixObserverDecodeBHist provenance)
          (prefixObserverDecodeBHist nameCert))
  | _ => none

private theorem prefixObserver_round_trip :
    ∀ x : PrefixObserverUp,
      prefixObserverFromEventFlow (prefixObserverToEventFlow x) = some x := by
  intro x
  cases x with
  | mk source prefixRow route check consumer ledger transport routes provenance nameCert =>
      change
        some
          (PrefixObserverUp.mk
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist source))
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist prefixRow))
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist route))
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist check))
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist consumer))
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist ledger))
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist transport))
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist routes))
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist provenance))
            (prefixObserverDecodeBHist (prefixObserverEncodeBHist nameCert))) =
          some
            (PrefixObserverUp.mk source prefixRow route check consumer ledger transport routes
              provenance nameCert)
      rw [prefixObserverDecode_encode_bhist source,
        prefixObserverDecode_encode_bhist prefixRow,
        prefixObserverDecode_encode_bhist route,
        prefixObserverDecode_encode_bhist check,
        prefixObserverDecode_encode_bhist consumer,
        prefixObserverDecode_encode_bhist ledger,
        prefixObserverDecode_encode_bhist transport,
        prefixObserverDecode_encode_bhist routes,
        prefixObserverDecode_encode_bhist provenance,
        prefixObserverDecode_encode_bhist nameCert]

private theorem prefixObserverToEventFlow_injective {x y : PrefixObserverUp} :
    prefixObserverToEventFlow x = prefixObserverToEventFlow y → x = y := by
  intro heq
  have hread :
      prefixObserverFromEventFlow (prefixObserverToEventFlow x) =
        prefixObserverFromEventFlow (prefixObserverToEventFlow y) :=
    congrArg prefixObserverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (prefixObserver_round_trip x).symm
      (Eq.trans hread (prefixObserver_round_trip y)))

instance prefixObserverBHistCarrier : BHistCarrier PrefixObserverUp where
  toEventFlow := prefixObserverToEventFlow
  fromEventFlow := prefixObserverFromEventFlow

instance prefixObserverChapterTasteGate : ChapterTasteGate PrefixObserverUp where
  round_trip := by
    intro x
    change prefixObserverFromEventFlow (prefixObserverToEventFlow x) = some x
    exact prefixObserver_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (prefixObserverToEventFlow_injective heq)

def taste_gate : ChapterTasteGate PrefixObserverUp :=
  prefixObserverChapterTasteGate

instance prefixObserverNontrivial : Nontrivial PrefixObserverUp where
  witness_pair :=
    ⟨PrefixObserverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PrefixObserverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

instance prefixObserverFieldFaithful : FieldFaithful PrefixObserverUp where
  fields
    | PrefixObserverUp.mk source prefixRow route check consumer ledger transport routes provenance
        nameCert =>
        [source, prefixRow, route, check, consumer, ledger, transport, routes, provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk source prefixRow route check consumer ledger transport routes provenance nameCert =>
        cases y with
        | mk source' prefixRow' route' check' consumer' ledger' transport' routes' provenance'
            nameCert' =>
            injection hfields with hSource hTail0
            injection hTail0 with hPrefix hTail1
            injection hTail1 with hRoute hTail2
            injection hTail2 with hCheck hTail3
            injection hTail3 with hConsumer hTail4
            injection hTail4 with hLedger hTail5
            injection hTail5 with hTransport hTail6
            injection hTail6 with hRoutes hTail7
            injection hTail7 with hProvenance hTail8
            injection hTail8 with hNameCert _hNil
            cases hSource
            cases hPrefix
            cases hRoute
            cases hCheck
            cases hConsumer
            cases hLedger
            cases hTransport
            cases hRoutes
            cases hProvenance
            cases hNameCert
            rfl

theorem PrefixObserverTasteGate_single_carrier_alignment :
    (∀ h : BHist, prefixObserverDecodeBHist (prefixObserverEncodeBHist h) = h) ∧
      (∀ x : PrefixObserverUp,
        prefixObserverFromEventFlow (prefixObserverToEventFlow x) = some x) ∧
        (∀ x y : PrefixObserverUp,
          prefixObserverToEventFlow x = prefixObserverToEventFlow y → x = y) ∧
          (∀ x y : PrefixObserverUp,
            FieldFaithful.fields x = FieldFaithful.fields y → x = y) ∧
            (∃ x y : PrefixObserverUp, x ≠ y) := by
  constructor
  · exact prefixObserverDecode_encode_bhist
  · constructor
    · exact prefixObserver_round_trip
    · constructor
      · intro x y heq
        exact prefixObserverToEventFlow_injective heq
      · constructor
        · exact FieldFaithful.field_faithful
        · exact
            ⟨prefixObserverNontrivial.witness_pair.1,
              prefixObserverNontrivial.witness_pair.2.1,
              prefixObserverNontrivial.witness_pair.2.2⟩

end BEDC.Derived.PrefixObserverUp
