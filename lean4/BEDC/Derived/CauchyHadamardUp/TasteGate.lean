import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyHadamardUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyHadamardUp : Type where
  | mk (A W R G D H C P N : BHist) : CauchyHadamardUp
  deriving DecidableEq

def cauchyHadamardEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyHadamardEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyHadamardEncodeBHist h

def cauchyHadamardDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyHadamardDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyHadamardDecodeBHist tail)

private theorem CauchyHadamardTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyHadamardFields : CauchyHadamardUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyHadamardUp.mk A W R G D H C P N => [A, W, R, G, D, H, C, P, N]

def cauchyHadamardToEventFlow : CauchyHadamardUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyHadamardFields x).map cauchyHadamardEncodeBHist

private def cauchyHadamardEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyHadamardEventAtDefault index rest

def cauchyHadamardFromEventFlow (ef : EventFlow) : Option CauchyHadamardUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyHadamardUp.mk
      (cauchyHadamardDecodeBHist (cauchyHadamardEventAtDefault 0 ef))
      (cauchyHadamardDecodeBHist (cauchyHadamardEventAtDefault 1 ef))
      (cauchyHadamardDecodeBHist (cauchyHadamardEventAtDefault 2 ef))
      (cauchyHadamardDecodeBHist (cauchyHadamardEventAtDefault 3 ef))
      (cauchyHadamardDecodeBHist (cauchyHadamardEventAtDefault 4 ef))
      (cauchyHadamardDecodeBHist (cauchyHadamardEventAtDefault 5 ef))
      (cauchyHadamardDecodeBHist (cauchyHadamardEventAtDefault 6 ef))
      (cauchyHadamardDecodeBHist (cauchyHadamardEventAtDefault 7 ef))
      (cauchyHadamardDecodeBHist (cauchyHadamardEventAtDefault 8 ef)))

private theorem CauchyHadamardTasteGate_single_carrier_alignment_round_trip
    (x : CauchyHadamardUp) :
    cauchyHadamardFromEventFlow (cauchyHadamardToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A W R G D H C P N =>
      change
        some
          (CauchyHadamardUp.mk
            (cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist A))
            (cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist W))
            (cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist R))
            (cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist G))
            (cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist D))
            (cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist H))
            (cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist C))
            (cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist P))
            (cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist N))) =
          some (CauchyHadamardUp.mk A W R G D H C P N)
      rw [CauchyHadamardTasteGate_single_carrier_alignment_decode A,
        CauchyHadamardTasteGate_single_carrier_alignment_decode W,
        CauchyHadamardTasteGate_single_carrier_alignment_decode R,
        CauchyHadamardTasteGate_single_carrier_alignment_decode G,
        CauchyHadamardTasteGate_single_carrier_alignment_decode D,
        CauchyHadamardTasteGate_single_carrier_alignment_decode H,
        CauchyHadamardTasteGate_single_carrier_alignment_decode C,
        CauchyHadamardTasteGate_single_carrier_alignment_decode P,
        CauchyHadamardTasteGate_single_carrier_alignment_decode N]

private theorem CauchyHadamardTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyHadamardUp} :
    cauchyHadamardToEventFlow x = cauchyHadamardToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyHadamardFromEventFlow (cauchyHadamardToEventFlow x) =
        cauchyHadamardFromEventFlow (cauchyHadamardToEventFlow y) :=
    congrArg cauchyHadamardFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyHadamardTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyHadamardTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyHadamardTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyHadamardUp, cauchyHadamardFields x = cauchyHadamardFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 W1 R1 G1 D1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 W2 R2 G2 D2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyHadamardBHistCarrier : BHistCarrier CauchyHadamardUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyHadamardToEventFlow
  fromEventFlow := cauchyHadamardFromEventFlow

instance cauchyHadamardChapterTasteGate : ChapterTasteGate CauchyHadamardUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyHadamardFromEventFlow (cauchyHadamardToEventFlow x) = some x
    exact CauchyHadamardTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyHadamardTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchyHadamardFieldFaithful : FieldFaithful CauchyHadamardUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyHadamardFields
  field_faithful := CauchyHadamardTasteGate_single_carrier_alignment_fields

instance cauchyHadamardNontrivial : Nontrivial CauchyHadamardUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyHadamardUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyHadamardUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyHadamardUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyHadamardChapterTasteGate

theorem CauchyHadamardTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchyHadamardUp) ∧
      (∀ h : BHist, cauchyHadamardDecodeBHist (cauchyHadamardEncodeBHist h) = h) ∧
        (∀ x : CauchyHadamardUp,
          cauchyHadamardFromEventFlow (cauchyHadamardToEventFlow x) = some x) ∧
          cauchyHadamardEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨⟨cauchyHadamardChapterTasteGate⟩,
      CauchyHadamardTasteGate_single_carrier_alignment_decode,
      CauchyHadamardTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.CauchyHadamardUp
