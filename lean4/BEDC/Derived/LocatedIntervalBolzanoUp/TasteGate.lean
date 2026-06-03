import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedIntervalBolzanoUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedIntervalBolzanoUp : Type where
  | mk
      (interval continuousMap endpointSign finiteNet bisection streamWindow dyadicTolerance
        regularReadback realSeal transport replay provenance localNameCert : BHist) :
      LocatedIntervalBolzanoUp
  deriving DecidableEq

def locatedIntervalBolzanoTag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b0, BMark.b1, BMark.b1, BMark.b0]

def locatedIntervalBolzanoEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedIntervalBolzanoEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedIntervalBolzanoEncodeBHist h

def locatedIntervalBolzanoDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedIntervalBolzanoDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedIntervalBolzanoDecodeBHist tail)

private theorem locatedIntervalBolzanoDecodeEncode :
    ∀ h : BHist,
      locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedIntervalBolzanoFields :
    LocatedIntervalBolzanoUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalBolzanoUp.mk interval continuousMap endpointSign finiteNet bisection
      streamWindow dyadicTolerance regularReadback realSeal transport replay provenance
      localNameCert =>
      [interval, continuousMap, endpointSign, finiteNet, bisection, streamWindow,
        dyadicTolerance, regularReadback, realSeal, transport, replay, provenance,
        localNameCert]

def locatedIntervalBolzanoToEventFlow :
    LocatedIntervalBolzanoUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedIntervalBolzanoUp.mk interval continuousMap endpointSign finiteNet bisection
      streamWindow dyadicTolerance regularReadback realSeal transport replay provenance
      localNameCert =>
      [locatedIntervalBolzanoTag,
        locatedIntervalBolzanoEncodeBHist interval,
        locatedIntervalBolzanoEncodeBHist continuousMap,
        locatedIntervalBolzanoEncodeBHist endpointSign,
        locatedIntervalBolzanoEncodeBHist finiteNet,
        locatedIntervalBolzanoEncodeBHist bisection,
        locatedIntervalBolzanoEncodeBHist streamWindow,
        locatedIntervalBolzanoEncodeBHist dyadicTolerance,
        locatedIntervalBolzanoEncodeBHist regularReadback,
        locatedIntervalBolzanoEncodeBHist realSeal,
        locatedIntervalBolzanoEncodeBHist transport,
        locatedIntervalBolzanoEncodeBHist replay,
        locatedIntervalBolzanoEncodeBHist provenance,
        locatedIntervalBolzanoEncodeBHist localNameCert]

private def locatedIntervalBolzanoEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => locatedIntervalBolzanoEventAtDefault index rest

def locatedIntervalBolzanoFromEventFlow :
    EventFlow → Option LocatedIntervalBolzanoUp := fun ef =>
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LocatedIntervalBolzanoUp.mk
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 1 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 2 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 3 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 4 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 5 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 6 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 7 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 8 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 9 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 10 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 11 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 12 ef))
      (locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEventAtDefault 13 ef)))

private theorem locatedIntervalBolzanoRoundTrip :
    ∀ x : LocatedIntervalBolzanoUp,
      locatedIntervalBolzanoFromEventFlow (locatedIntervalBolzanoToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk interval continuousMap endpointSign finiteNet bisection streamWindow dyadicTolerance
      regularReadback realSeal transport replay provenance localNameCert =>
      change
        some
          (LocatedIntervalBolzanoUp.mk
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist interval))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist continuousMap))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist endpointSign))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist finiteNet))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist bisection))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist streamWindow))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist dyadicTolerance))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist regularReadback))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist realSeal))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist transport))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist replay))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist provenance))
            (locatedIntervalBolzanoDecodeBHist
              (locatedIntervalBolzanoEncodeBHist localNameCert))) =
          some
            (LocatedIntervalBolzanoUp.mk interval continuousMap endpointSign finiteNet
              bisection streamWindow dyadicTolerance regularReadback realSeal transport replay
              provenance localNameCert)
      rw [locatedIntervalBolzanoDecodeEncode interval,
        locatedIntervalBolzanoDecodeEncode continuousMap,
        locatedIntervalBolzanoDecodeEncode endpointSign,
        locatedIntervalBolzanoDecodeEncode finiteNet,
        locatedIntervalBolzanoDecodeEncode bisection,
        locatedIntervalBolzanoDecodeEncode streamWindow,
        locatedIntervalBolzanoDecodeEncode dyadicTolerance,
        locatedIntervalBolzanoDecodeEncode regularReadback,
        locatedIntervalBolzanoDecodeEncode realSeal,
        locatedIntervalBolzanoDecodeEncode transport,
        locatedIntervalBolzanoDecodeEncode replay,
        locatedIntervalBolzanoDecodeEncode provenance,
        locatedIntervalBolzanoDecodeEncode localNameCert]

private theorem locatedIntervalBolzanoToEventFlow_injective
    {x y : LocatedIntervalBolzanoUp} :
    locatedIntervalBolzanoToEventFlow x = locatedIntervalBolzanoToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedIntervalBolzanoFromEventFlow (locatedIntervalBolzanoToEventFlow x) =
        locatedIntervalBolzanoFromEventFlow (locatedIntervalBolzanoToEventFlow y) :=
    congrArg locatedIntervalBolzanoFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (locatedIntervalBolzanoRoundTrip x).symm
      (Eq.trans hread (locatedIntervalBolzanoRoundTrip y)))

private theorem locatedIntervalBolzanoFieldFaithfulProof :
    ∀ x y : LocatedIntervalBolzanoUp,
      locatedIntervalBolzanoFields x = locatedIntervalBolzanoFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk interval1 continuousMap1 endpointSign1 finiteNet1 bisection1 streamWindow1
      dyadicTolerance1 regularReadback1 realSeal1 transport1 replay1 provenance1
      localNameCert1 =>
      cases y with
      | mk interval2 continuousMap2 endpointSign2 finiteNet2 bisection2 streamWindow2
          dyadicTolerance2 regularReadback2 realSeal2 transport2 replay2 provenance2
          localNameCert2 =>
          cases hfields
          rfl

instance locatedIntervalBolzanoBHistCarrier : BHistCarrier LocatedIntervalBolzanoUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedIntervalBolzanoToEventFlow
  fromEventFlow := locatedIntervalBolzanoFromEventFlow

instance locatedIntervalBolzanoChapterTasteGate :
    ChapterTasteGate LocatedIntervalBolzanoUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedIntervalBolzanoFromEventFlow (locatedIntervalBolzanoToEventFlow x) = some x
    exact locatedIntervalBolzanoRoundTrip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedIntervalBolzanoToEventFlow_injective heq)

instance locatedIntervalBolzanoFieldFaithful :
    FieldFaithful LocatedIntervalBolzanoUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedIntervalBolzanoFields
  field_faithful := locatedIntervalBolzanoFieldFaithfulProof

instance locatedIntervalBolzanoNontrivial :
    Nontrivial LocatedIntervalBolzanoUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedIntervalBolzanoUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      LocatedIntervalBolzanoUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedIntervalBolzanoUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedIntervalBolzanoChapterTasteGate

theorem LocatedIntervalBolzanoTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedIntervalBolzanoUp) ∧
      Nonempty (FieldFaithful LocatedIntervalBolzanoUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedIntervalBolzanoUp) ∧
          (∀ h : BHist,
            locatedIntervalBolzanoDecodeBHist (locatedIntervalBolzanoEncodeBHist h) = h) ∧
            (∀ x : LocatedIntervalBolzanoUp,
              locatedIntervalBolzanoFromEventFlow (locatedIntervalBolzanoToEventFlow x) =
                some x) ∧
              (∀ x y : LocatedIntervalBolzanoUp,
                locatedIntervalBolzanoToEventFlow x = locatedIntervalBolzanoToEventFlow y →
                  x = y) ∧
                locatedIntervalBolzanoEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨Nonempty.intro locatedIntervalBolzanoChapterTasteGate,
      Nonempty.intro locatedIntervalBolzanoFieldFaithful,
      Nonempty.intro locatedIntervalBolzanoNontrivial,
      locatedIntervalBolzanoDecodeEncode,
      locatedIntervalBolzanoRoundTrip,
      (fun _ _ heq => locatedIntervalBolzanoToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedIntervalBolzanoUp
