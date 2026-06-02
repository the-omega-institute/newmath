import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier : Type where
  | mk (L U M R V W Q A H C P N : BHist) :
      dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier
  deriving DecidableEq

def dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist h
  | BHist.e1 h => BMark.b1 ::
      dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist h

def dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist tail)

private theorem dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def dyadic_interval_cover_taste_gate_single_carrier_alignment_fields :
    dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier.mk
      L U M R V W Q A H C P N => [L, U, M, R, V, W, Q, A, H, C, P, N]

def dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow :
    dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadic_interval_cover_taste_gate_single_carrier_alignment_fields x).map
      dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist

private def dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at index rest

def dyadic_interval_cover_taste_gate_single_carrier_alignment_from_event_flow
    (ef : EventFlow) :
    Option dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier.mk
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 0 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 1 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 2 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 3 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 4 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 5 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 6 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 7 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 8 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 9 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 10 ef))
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_event_at 11 ef)))

private theorem dyadic_interval_cover_taste_gate_single_carrier_alignment_round_trip
    (x : dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier) :
    dyadic_interval_cover_taste_gate_single_carrier_alignment_from_event_flow
      (dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L U M R V W Q A H C P N =>
      change
        some
          (dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier.mk
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist L))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist U))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist M))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist R))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist V))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist W))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist Q))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist A))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist H))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist C))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist P))
            (dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
              (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist N))) =
          some (dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier.mk
            L U M R V W Q A H C P N)
      rw [dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode L,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode U,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode M,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode R,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode V,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode W,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode Q,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode A,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode H,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode C,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode P,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode N]

private theorem dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow_injective
    {x y : dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier} :
    dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow x =
      dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadic_interval_cover_taste_gate_single_carrier_alignment_from_event_flow
          (dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow x) =
        dyadic_interval_cover_taste_gate_single_carrier_alignment_from_event_flow
          (dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow y) :=
    congrArg dyadic_interval_cover_taste_gate_single_carrier_alignment_from_event_flow heq
  exact Option.some.inj
    (Eq.trans (dyadic_interval_cover_taste_gate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (dyadic_interval_cover_taste_gate_single_carrier_alignment_round_trip y)))

theorem DyadicIntervalCoverTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_bhist
        (dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist h) = h) ∧
      (∀ x : dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier,
        dyadic_interval_cover_taste_gate_single_carrier_alignment_from_event_flow
          (dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow x) = some x) ∧
        (∀ x y : dyadic_interval_cover_taste_gate_single_carrier_alignment_carrier,
          dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow x =
            dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow y → x = y) ∧
          dyadic_interval_cover_taste_gate_single_carrier_alignment_encode_bhist
            BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨dyadic_interval_cover_taste_gate_single_carrier_alignment_decode_encode,
      dyadic_interval_cover_taste_gate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        dyadic_interval_cover_taste_gate_single_carrier_alignment_to_event_flow_injective heq),
      rfl⟩

end BEDC.Derived.DyadicIntervalCoverUp
