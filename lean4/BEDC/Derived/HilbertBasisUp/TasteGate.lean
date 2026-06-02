import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HilbertBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive HilbertBasisUp : Type where
  | mk (P R C I G B H K Q N : BHist) : HilbertBasisUp
  deriving DecidableEq

def hilbertBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hilbertBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hilbertBasisEncodeBHist h

def hilbertBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hilbertBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hilbertBasisDecodeBHist tail)

private theorem HilbertBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, hilbertBasisDecodeBHist (hilbertBasisEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hilbertBasisFields : HilbertBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HilbertBasisUp.mk P R C I G B H K Q N => [P, R, C, I, G, B, H, K, Q, N]

def hilbertBasisToEventFlow : HilbertBasisUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (hilbertBasisFields x).map hilbertBasisEncodeBHist

private def hilbertBasisEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => hilbertBasisEventAtDefault index rest

def hilbertBasisFromEventFlow (ef : EventFlow) : Option HilbertBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (HilbertBasisUp.mk
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 0 ef))
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 1 ef))
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 2 ef))
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 3 ef))
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 4 ef))
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 5 ef))
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 6 ef))
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 7 ef))
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 8 ef))
      (hilbertBasisDecodeBHist (hilbertBasisEventAtDefault 9 ef)))

private theorem HilbertBasisTasteGate_single_carrier_alignment_round_trip
    (x : HilbertBasisUp) :
    hilbertBasisFromEventFlow (hilbertBasisToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk P R C I G B H K Q N =>
      change
        some
          (HilbertBasisUp.mk
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist P))
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist R))
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist C))
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist I))
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist G))
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist B))
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist H))
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist K))
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist Q))
            (hilbertBasisDecodeBHist (hilbertBasisEncodeBHist N))) =
          some (HilbertBasisUp.mk P R C I G B H K Q N)
      rw [HilbertBasisTasteGate_single_carrier_alignment_decode_encode P,
        HilbertBasisTasteGate_single_carrier_alignment_decode_encode R,
        HilbertBasisTasteGate_single_carrier_alignment_decode_encode C,
        HilbertBasisTasteGate_single_carrier_alignment_decode_encode I,
        HilbertBasisTasteGate_single_carrier_alignment_decode_encode G,
        HilbertBasisTasteGate_single_carrier_alignment_decode_encode B,
        HilbertBasisTasteGate_single_carrier_alignment_decode_encode H,
        HilbertBasisTasteGate_single_carrier_alignment_decode_encode K,
        HilbertBasisTasteGate_single_carrier_alignment_decode_encode Q,
        HilbertBasisTasteGate_single_carrier_alignment_decode_encode N]

private theorem HilbertBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : HilbertBasisUp} :
    hilbertBasisToEventFlow x = hilbertBasisToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hilbertBasisFromEventFlow (hilbertBasisToEventFlow x) =
        hilbertBasisFromEventFlow (hilbertBasisToEventFlow y) :=
    congrArg hilbertBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (HilbertBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (HilbertBasisTasteGate_single_carrier_alignment_round_trip y)))

private theorem HilbertBasisTasteGate_single_carrier_alignment_fields :
    ∀ x y : HilbertBasisUp, hilbertBasisFields x = hilbertBasisFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk P1 R1 C1 I1 G1 B1 H1 K1 Q1 N1 =>
      cases y with
      | mk P2 R2 C2 I2 G2 B2 H2 K2 Q2 N2 =>
          cases hfields
          rfl

instance hilbertBasisBHistCarrier : BHistCarrier HilbertBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hilbertBasisToEventFlow
  fromEventFlow := hilbertBasisFromEventFlow

instance hilbertBasisChapterTasteGate : ChapterTasteGate HilbertBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hilbertBasisFromEventFlow (hilbertBasisToEventFlow x) = some x
    exact HilbertBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (HilbertBasisTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance hilbertBasisFieldFaithful : FieldFaithful HilbertBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hilbertBasisFields
  field_faithful := HilbertBasisTasteGate_single_carrier_alignment_fields

instance hilbertBasisNontrivial : Nontrivial HilbertBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HilbertBasisUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HilbertBasisUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate HilbertBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  hilbertBasisChapterTasteGate

theorem HilbertBasisTasteGate_single_carrier_alignment :
    ChapterTasteGate HilbertBasisUp := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact hilbertBasisChapterTasteGate

end BEDC.Derived.HilbertBasisUp
