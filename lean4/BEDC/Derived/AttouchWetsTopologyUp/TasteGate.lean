import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AttouchWetsTopologyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AttouchWetsTopologyUp : Type where
  | mk (M H D W R E Q T C P N : BHist) : AttouchWetsTopologyUp
  deriving DecidableEq

def attouchWetsTopologyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: attouchWetsTopologyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: attouchWetsTopologyEncodeBHist h

def attouchWetsTopologyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (attouchWetsTopologyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (attouchWetsTopologyDecodeBHist tail)

private theorem attouchWetsTopology_decode_encode_bhist :
    ∀ h : BHist,
      attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def attouchWetsTopologyFields : AttouchWetsTopologyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AttouchWetsTopologyUp.mk M H D W R E Q T C P N => [M, H, D, W, R, E, Q, T, C, P, N]

def attouchWetsTopologyToEventFlow : AttouchWetsTopologyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (attouchWetsTopologyFields x).map attouchWetsTopologyEncodeBHist

def attouchWetsTopologyFromEventFlow : EventFlow → Option AttouchWetsTopologyUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: H :: D :: W :: R :: E :: Q :: T :: C :: P :: N :: [] =>
      some
        (AttouchWetsTopologyUp.mk
          (attouchWetsTopologyDecodeBHist M)
          (attouchWetsTopologyDecodeBHist H)
          (attouchWetsTopologyDecodeBHist D)
          (attouchWetsTopologyDecodeBHist W)
          (attouchWetsTopologyDecodeBHist R)
          (attouchWetsTopologyDecodeBHist E)
          (attouchWetsTopologyDecodeBHist Q)
          (attouchWetsTopologyDecodeBHist T)
          (attouchWetsTopologyDecodeBHist C)
          (attouchWetsTopologyDecodeBHist P)
          (attouchWetsTopologyDecodeBHist N))
  | _ => none

private theorem attouchWetsTopology_round_trip :
    ∀ x : AttouchWetsTopologyUp,
      attouchWetsTopologyFromEventFlow (attouchWetsTopologyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M H D W R E Q T C P N =>
      change
        some
            (AttouchWetsTopologyUp.mk
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist M))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist H))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist D))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist W))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist R))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist E))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist Q))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist T))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist C))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist P))
              (attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist N))) =
          some (AttouchWetsTopologyUp.mk M H D W R E Q T C P N)
      rw [attouchWetsTopology_decode_encode_bhist M,
        attouchWetsTopology_decode_encode_bhist H,
        attouchWetsTopology_decode_encode_bhist D,
        attouchWetsTopology_decode_encode_bhist W,
        attouchWetsTopology_decode_encode_bhist R,
        attouchWetsTopology_decode_encode_bhist E,
        attouchWetsTopology_decode_encode_bhist Q,
        attouchWetsTopology_decode_encode_bhist T,
        attouchWetsTopology_decode_encode_bhist C,
        attouchWetsTopology_decode_encode_bhist P,
        attouchWetsTopology_decode_encode_bhist N]

private theorem attouchWetsTopologyToEventFlow_injective {x y : AttouchWetsTopologyUp} :
    attouchWetsTopologyToEventFlow x = attouchWetsTopologyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      attouchWetsTopologyFromEventFlow (attouchWetsTopologyToEventFlow x) =
        attouchWetsTopologyFromEventFlow (attouchWetsTopologyToEventFlow y) :=
    congrArg attouchWetsTopologyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (attouchWetsTopology_round_trip x).symm
      (Eq.trans hread (attouchWetsTopology_round_trip y)))

instance attouchWetsTopologyBHistCarrier : BHistCarrier AttouchWetsTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := attouchWetsTopologyToEventFlow
  fromEventFlow := attouchWetsTopologyFromEventFlow

instance attouchWetsTopologyChapterTasteGate : ChapterTasteGate AttouchWetsTopologyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change attouchWetsTopologyFromEventFlow (attouchWetsTopologyToEventFlow x) = some x
    exact attouchWetsTopology_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (attouchWetsTopologyToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AttouchWetsTopologyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  attouchWetsTopologyChapterTasteGate

theorem AttouchWetsTopologyTasteGate_single_carrier_alignment :
    ∀ x : AttouchWetsTopologyUp,
      ∃ M H D W R E Q T C P N : BHist,
        x = AttouchWetsTopologyUp.mk M H D W R E Q T C P N ∧
          attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist M) = M ∧
            attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist H) = H ∧
              attouchWetsTopologyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark BHistCarrier ChapterTasteGate
  have decodeEncode :
      ∀ h : BHist,
        attouchWetsTopologyDecodeBHist (attouchWetsTopologyEncodeBHist h) = h := by
    intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  intro x
  cases x with
  | mk M H D W R E Q T C P N =>
      exact
        ⟨M, H, D, W, R, E, Q, T, C, P, N, rfl, decodeEncode M, decodeEncode H, rfl⟩

end BEDC.Derived.AttouchWetsTopologyUp
