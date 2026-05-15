import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HostTotalTraceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HostTotalTraceUp : Type where
  | mk :
      (host fuel readback endpoint timeout transport route provenance name : BHist) →
      HostTotalTraceUp
  deriving DecidableEq

def hostTotalTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hostTotalTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hostTotalTraceEncodeBHist h

def hostTotalTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hostTotalTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hostTotalTraceDecodeBHist tail)

private theorem hostTotalTrace_decode_encode_bhist :
    ∀ h : BHist, hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def hostTotalTraceToEventFlow : HostTotalTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | HostTotalTraceUp.mk host fuel readback endpoint timeout transport route provenance name =>
      [[BMark.b0],
        hostTotalTraceEncodeBHist host,
        [BMark.b1, BMark.b0],
        hostTotalTraceEncodeBHist fuel,
        [BMark.b1, BMark.b1, BMark.b0],
        hostTotalTraceEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostTotalTraceEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostTotalTraceEncodeBHist timeout,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostTotalTraceEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        hostTotalTraceEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        hostTotalTraceEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        hostTotalTraceEncodeBHist name]

private def hostTotalTraceRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => hostTotalTraceRawAt n rest

private def hostTotalTraceLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => hostTotalTraceLengthEq n rest

def hostTotalTraceFromEventFlow : EventFlow → Option HostTotalTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match hostTotalTraceLengthEq 18 flow with
      | true =>
          some
            (HostTotalTraceUp.mk
              (hostTotalTraceDecodeBHist (hostTotalTraceRawAt 1 flow))
              (hostTotalTraceDecodeBHist (hostTotalTraceRawAt 3 flow))
              (hostTotalTraceDecodeBHist (hostTotalTraceRawAt 5 flow))
              (hostTotalTraceDecodeBHist (hostTotalTraceRawAt 7 flow))
              (hostTotalTraceDecodeBHist (hostTotalTraceRawAt 9 flow))
              (hostTotalTraceDecodeBHist (hostTotalTraceRawAt 11 flow))
              (hostTotalTraceDecodeBHist (hostTotalTraceRawAt 13 flow))
              (hostTotalTraceDecodeBHist (hostTotalTraceRawAt 15 flow))
              (hostTotalTraceDecodeBHist (hostTotalTraceRawAt 17 flow)))
      | false => none

private theorem hostTotalTrace_round_trip :
    ∀ x : HostTotalTraceUp,
      hostTotalTraceFromEventFlow (hostTotalTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk host fuel readback endpoint timeout transport route provenance name =>
      change
        some
          (HostTotalTraceUp.mk
            (hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist host))
            (hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist fuel))
            (hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist readback))
            (hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist endpoint))
            (hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist timeout))
            (hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist transport))
            (hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist route))
            (hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist provenance))
            (hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist name))) =
          some
            (HostTotalTraceUp.mk host fuel readback endpoint timeout transport route
              provenance name)
      rw [hostTotalTrace_decode_encode_bhist host, hostTotalTrace_decode_encode_bhist fuel,
        hostTotalTrace_decode_encode_bhist readback,
        hostTotalTrace_decode_encode_bhist endpoint,
        hostTotalTrace_decode_encode_bhist timeout,
        hostTotalTrace_decode_encode_bhist transport,
        hostTotalTrace_decode_encode_bhist route,
        hostTotalTrace_decode_encode_bhist provenance,
        hostTotalTrace_decode_encode_bhist name]

private theorem hostTotalTraceToEventFlow_injective {x y : HostTotalTraceUp} :
    hostTotalTraceToEventFlow x = hostTotalTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hostTotalTraceFromEventFlow (hostTotalTraceToEventFlow x) =
        hostTotalTraceFromEventFlow (hostTotalTraceToEventFlow y) :=
    congrArg hostTotalTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hostTotalTrace_round_trip x).symm
      (Eq.trans hread (hostTotalTrace_round_trip y)))

instance hostTotalTraceBHistCarrier : BHistCarrier HostTotalTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hostTotalTraceToEventFlow
  fromEventFlow := hostTotalTraceFromEventFlow

instance hostTotalTraceChapterTasteGate : ChapterTasteGate HostTotalTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hostTotalTraceFromEventFlow (hostTotalTraceToEventFlow x) = some x
    exact hostTotalTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hostTotalTraceToEventFlow_injective heq)

instance hostTotalTraceFieldFaithful : FieldFaithful HostTotalTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | HostTotalTraceUp.mk host fuel readback endpoint timeout transport route provenance
        name =>
        [host, fuel, readback, endpoint, timeout, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk host1 fuel1 readback1 endpoint1 timeout1 transport1 route1 provenance1 name1 =>
        cases y with
        | mk host2 fuel2 readback2 endpoint2 timeout2 transport2 route2 provenance2 name2 =>
            cases h
            rfl

instance hostTotalTraceNontrivial : Nontrivial HostTotalTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HostTotalTraceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HostTotalTraceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HostTotalTraceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hostTotalTraceChapterTasteGate

theorem HostTotalTraceTasteGate_single_carrier_alignment :
    (∀ h : BHist, hostTotalTraceDecodeBHist (hostTotalTraceEncodeBHist h) = h) ∧
      (∀ x : HostTotalTraceUp,
        hostTotalTraceFromEventFlow (hostTotalTraceToEventFlow x) = some x) ∧
        (∀ x y : HostTotalTraceUp,
          hostTotalTraceToEventFlow x = hostTotalTraceToEventFlow y → x = y) ∧
          hostTotalTraceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨hostTotalTrace_decode_encode_bhist, hostTotalTrace_round_trip,
      by
        intro x y heq
        exact hostTotalTraceToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.HostTotalTraceUp
