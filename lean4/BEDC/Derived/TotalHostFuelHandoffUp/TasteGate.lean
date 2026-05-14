import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TotalHostFuelHandoffUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TotalHostFuelHandoffUp : Type where
  | mk :
      (host fuel substrate trace readback refusal transport route provenance name : BHist) →
      TotalHostFuelHandoffUp
  deriving DecidableEq

def totalHostFuelHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: totalHostFuelHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: totalHostFuelHandoffEncodeBHist h

def totalHostFuelHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (totalHostFuelHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (totalHostFuelHandoffDecodeBHist tail)

private theorem totalHostFuelHandoff_decode_encode_bhist :
    ∀ h : BHist,
      totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def totalHostFuelHandoffToEventFlow : TotalHostFuelHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TotalHostFuelHandoffUp.mk host fuel substrate trace readback refusal transport route
      provenance name =>
      [[BMark.b0],
        totalHostFuelHandoffEncodeBHist host,
        [BMark.b1, BMark.b0],
        totalHostFuelHandoffEncodeBHist fuel,
        [BMark.b1, BMark.b1, BMark.b0],
        totalHostFuelHandoffEncodeBHist substrate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totalHostFuelHandoffEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totalHostFuelHandoffEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totalHostFuelHandoffEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        totalHostFuelHandoffEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        totalHostFuelHandoffEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        totalHostFuelHandoffEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        totalHostFuelHandoffEncodeBHist name]

private def totalHostFuelHandoffRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => totalHostFuelHandoffRawAt n rest

private def totalHostFuelHandoffLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => totalHostFuelHandoffLengthEq n rest

def totalHostFuelHandoffFromEventFlow : EventFlow → Option TotalHostFuelHandoffUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match totalHostFuelHandoffLengthEq 20 flow with
      | true =>
          some
            (TotalHostFuelHandoffUp.mk
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 1 flow))
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 3 flow))
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 5 flow))
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 7 flow))
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 9 flow))
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 11 flow))
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 13 flow))
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 15 flow))
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 17 flow))
              (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffRawAt 19 flow)))
      | false => none

private theorem totalHostFuelHandoff_round_trip :
    ∀ x : TotalHostFuelHandoffUp,
      totalHostFuelHandoffFromEventFlow (totalHostFuelHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk host fuel substrate trace readback refusal transport route provenance name =>
      change
        some
          (TotalHostFuelHandoffUp.mk
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist host))
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist fuel))
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist substrate))
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist trace))
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist readback))
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist refusal))
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist transport))
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist route))
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist provenance))
            (totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist name))) =
          some
            (TotalHostFuelHandoffUp.mk host fuel substrate trace readback refusal transport
              route provenance name)
      rw [totalHostFuelHandoff_decode_encode_bhist host,
        totalHostFuelHandoff_decode_encode_bhist fuel,
        totalHostFuelHandoff_decode_encode_bhist substrate,
        totalHostFuelHandoff_decode_encode_bhist trace,
        totalHostFuelHandoff_decode_encode_bhist readback,
        totalHostFuelHandoff_decode_encode_bhist refusal,
        totalHostFuelHandoff_decode_encode_bhist transport,
        totalHostFuelHandoff_decode_encode_bhist route,
        totalHostFuelHandoff_decode_encode_bhist provenance,
        totalHostFuelHandoff_decode_encode_bhist name]

private theorem totalHostFuelHandoffToEventFlow_injective {x y : TotalHostFuelHandoffUp} :
    totalHostFuelHandoffToEventFlow x = totalHostFuelHandoffToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      totalHostFuelHandoffFromEventFlow (totalHostFuelHandoffToEventFlow x) =
        totalHostFuelHandoffFromEventFlow (totalHostFuelHandoffToEventFlow y) :=
    congrArg totalHostFuelHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (totalHostFuelHandoff_round_trip x).symm
      (Eq.trans hread (totalHostFuelHandoff_round_trip y)))

instance totalHostFuelHandoffBHistCarrier : BHistCarrier TotalHostFuelHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := totalHostFuelHandoffToEventFlow
  fromEventFlow := totalHostFuelHandoffFromEventFlow

instance totalHostFuelHandoffChapterTasteGate :
    ChapterTasteGate TotalHostFuelHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change totalHostFuelHandoffFromEventFlow (totalHostFuelHandoffToEventFlow x) = some x
    exact totalHostFuelHandoff_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (totalHostFuelHandoffToEventFlow_injective heq)

instance totalHostFuelHandoffFieldFaithful : FieldFaithful TotalHostFuelHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | TotalHostFuelHandoffUp.mk host fuel substrate trace readback refusal transport route
        provenance name =>
        [host, fuel, substrate, trace, readback, refusal, transport, route, provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk host1 fuel1 substrate1 trace1 readback1 refusal1 transport1 route1 provenance1 name1 =>
        cases y with
        | mk host2 fuel2 substrate2 trace2 readback2 refusal2 transport2 route2 provenance2
            name2 =>
            cases h
            rfl

instance totalHostFuelHandoffNontrivial : Nontrivial TotalHostFuelHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TotalHostFuelHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TotalHostFuelHandoffUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TotalHostFuelHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  totalHostFuelHandoffChapterTasteGate

theorem TotalHostFuelHandoffTasteGate_single_carrier_alignment :
    ChapterTasteGate TotalHostFuelHandoffUp ∧
      Nonempty (Nontrivial TotalHostFuelHandoffUp) ∧
        Nonempty (FieldFaithful TotalHostFuelHandoffUp) ∧
          (∀ h : BHist,
            totalHostFuelHandoffDecodeBHist (totalHostFuelHandoffEncodeBHist h) = h) ∧
            (∀ x y : TotalHostFuelHandoffUp,
              totalHostFuelHandoffToEventFlow x =
                totalHostFuelHandoffToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨totalHostFuelHandoffChapterTasteGate, ⟨totalHostFuelHandoffNontrivial⟩,
      ⟨totalHostFuelHandoffFieldFaithful⟩, totalHostFuelHandoff_decode_encode_bhist,
      by
        intro x y heq
        exact totalHostFuelHandoffToEventFlow_injective heq⟩

end BEDC.Derived.TotalHostFuelHandoffUp
