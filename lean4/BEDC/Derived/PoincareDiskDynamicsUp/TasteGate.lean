import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoincareDiskDynamicsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoincareDiskDynamicsUp : Type where
  | mk (U Phi G B F V A H C P N : BHist) : PoincareDiskDynamicsUp
  deriving DecidableEq

def poincareDiskDynamicsEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poincareDiskDynamicsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poincareDiskDynamicsEncodeBHist h

def poincareDiskDynamicsDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poincareDiskDynamicsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poincareDiskDynamicsDecodeBHist tail)

private theorem poincareDiskDynamics_decode_encode_bhist :
    ∀ h : BHist, poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def poincareDiskDynamicsFields : PoincareDiskDynamicsUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PoincareDiskDynamicsUp.mk U Phi G B F V A H C P N => [U, Phi, G, B, F, V, A, H, C, P, N]

def poincareDiskDynamicsToEventFlow : PoincareDiskDynamicsUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (poincareDiskDynamicsFields x).map poincareDiskDynamicsEncodeBHist

private def poincareDiskDynamicsRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => poincareDiskDynamicsRawAt n rest

def poincareDiskDynamicsFromEventFlow : EventFlow → Option PoincareDiskDynamicsUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      some
        (PoincareDiskDynamicsUp.mk
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 0 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 1 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 2 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 3 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 4 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 5 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 6 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 7 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 8 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 9 flow))
          (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsRawAt 10 flow)))

private theorem poincareDiskDynamics_round_trip :
    ∀ x : PoincareDiskDynamicsUp,
      poincareDiskDynamicsFromEventFlow (poincareDiskDynamicsToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk U Phi G B F V A H C P N =>
      change
        some
          (PoincareDiskDynamicsUp.mk
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist U))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist Phi))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist G))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist B))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist F))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist V))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist A))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist H))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist C))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist P))
            (poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist N))) =
          some (PoincareDiskDynamicsUp.mk U Phi G B F V A H C P N)
      rw [poincareDiskDynamics_decode_encode_bhist U,
        poincareDiskDynamics_decode_encode_bhist Phi,
        poincareDiskDynamics_decode_encode_bhist G,
        poincareDiskDynamics_decode_encode_bhist B,
        poincareDiskDynamics_decode_encode_bhist F,
        poincareDiskDynamics_decode_encode_bhist V,
        poincareDiskDynamics_decode_encode_bhist A,
        poincareDiskDynamics_decode_encode_bhist H,
        poincareDiskDynamics_decode_encode_bhist C,
        poincareDiskDynamics_decode_encode_bhist P,
        poincareDiskDynamics_decode_encode_bhist N]

private theorem poincareDiskDynamicsToEventFlow_injective {x y : PoincareDiskDynamicsUp} :
    poincareDiskDynamicsToEventFlow x = poincareDiskDynamicsToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poincareDiskDynamicsFromEventFlow (poincareDiskDynamicsToEventFlow x) =
        poincareDiskDynamicsFromEventFlow (poincareDiskDynamicsToEventFlow y) :=
    congrArg poincareDiskDynamicsFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (poincareDiskDynamics_round_trip x).symm
      (Eq.trans hread (poincareDiskDynamics_round_trip y)))

private theorem poincareDiskDynamics_field_faithful :
    ∀ x y : PoincareDiskDynamicsUp,
      poincareDiskDynamicsFields x = poincareDiskDynamicsFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk U1 Phi1 G1 B1 F1 V1 A1 H1 C1 P1 N1 =>
      cases y with
      | mk U2 Phi2 G2 B2 F2 V2 A2 H2 C2 P2 N2 =>
          cases h
          rfl

instance poincareDiskDynamicsBHistCarrier : BHistCarrier PoincareDiskDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poincareDiskDynamicsToEventFlow
  fromEventFlow := poincareDiskDynamicsFromEventFlow

instance poincareDiskDynamicsChapterTasteGate :
    ChapterTasteGate PoincareDiskDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change poincareDiskDynamicsFromEventFlow (poincareDiskDynamicsToEventFlow x) = some x
    exact poincareDiskDynamics_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (poincareDiskDynamicsToEventFlow_injective heq)

instance poincareDiskDynamicsFieldFaithful : FieldFaithful PoincareDiskDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := poincareDiskDynamicsFields
  field_faithful := poincareDiskDynamics_field_faithful

instance poincareDiskDynamicsNontrivial : Nontrivial PoincareDiskDynamicsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PoincareDiskDynamicsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PoincareDiskDynamicsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PoincareDiskDynamicsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  poincareDiskDynamicsChapterTasteGate

theorem PoincareDiskDynamicsTasteGate_single_carrier_alignment :
    (∀ h : BHist, poincareDiskDynamicsDecodeBHist (poincareDiskDynamicsEncodeBHist h) = h) ∧
      (∀ x : PoincareDiskDynamicsUp,
        poincareDiskDynamicsFromEventFlow (poincareDiskDynamicsToEventFlow x) = some x) ∧
        (∀ x y : PoincareDiskDynamicsUp,
          poincareDiskDynamicsToEventFlow x = poincareDiskDynamicsToEventFlow y → x = y) ∧
          poincareDiskDynamicsEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨poincareDiskDynamics_decode_encode_bhist,
      poincareDiskDynamics_round_trip,
      by
        intro x y heq
        exact poincareDiskDynamicsToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.PoincareDiskDynamicsUp
