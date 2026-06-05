import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TaylorPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TaylorPolynomialUp : Type where
  | mk
      (center order derivative jet polynomial evaluation readback endpointSeal transport replay
        provenance localName : BHist) : TaylorPolynomialUp
  deriving DecidableEq

def taylorPolynomialEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: taylorPolynomialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: taylorPolynomialEncodeBHist h

def taylorPolynomialDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (taylorPolynomialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (taylorPolynomialDecodeBHist tail)

private theorem TaylorPolynomialTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def taylorPolynomialFields : TaylorPolynomialUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TaylorPolynomialUp.mk center order derivative jet polynomial evaluation readback endpointSeal
      transport replay provenance localName =>
      [center, order, derivative, jet, polynomial, evaluation, readback, endpointSeal,
        transport, replay, provenance, localName]

def taylorPolynomialToEventFlow : TaylorPolynomialUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (taylorPolynomialFields x).map taylorPolynomialEncodeBHist

private def taylorPolynomialEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => taylorPolynomialEventAtDefault index rest

def taylorPolynomialFromEventFlow (ef : EventFlow) : Option TaylorPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TaylorPolynomialUp.mk
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 0 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 1 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 2 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 3 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 4 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 5 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 6 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 7 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 8 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 9 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 10 ef))
      (taylorPolynomialDecodeBHist (taylorPolynomialEventAtDefault 11 ef)))

private theorem TaylorPolynomialTasteGate_single_carrier_alignment_round_trip
    (x : TaylorPolynomialUp) :
    taylorPolynomialFromEventFlow (taylorPolynomialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk center order derivative jet polynomial evaluation readback endpointSeal transport replay
      provenance localName =>
      change
        some
          (TaylorPolynomialUp.mk
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist center))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist order))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist derivative))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist jet))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist polynomial))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist evaluation))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist readback))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist endpointSeal))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist transport))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist replay))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist provenance))
            (taylorPolynomialDecodeBHist (taylorPolynomialEncodeBHist localName))) =
          some
            (TaylorPolynomialUp.mk center order derivative jet polynomial evaluation readback
              endpointSeal transport replay provenance localName)
      rw [TaylorPolynomialTasteGate_single_carrier_alignment_decode center,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode order,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode derivative,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode jet,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode polynomial,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode evaluation,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode readback,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode endpointSeal,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode transport,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode replay,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode provenance,
        TaylorPolynomialTasteGate_single_carrier_alignment_decode localName]

private theorem TaylorPolynomialTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : TaylorPolynomialUp} :
    taylorPolynomialToEventFlow x = taylorPolynomialToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      taylorPolynomialFromEventFlow (taylorPolynomialToEventFlow x) =
        taylorPolynomialFromEventFlow (taylorPolynomialToEventFlow y) :=
    congrArg taylorPolynomialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (TaylorPolynomialTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (TaylorPolynomialTasteGate_single_carrier_alignment_round_trip y)))

private theorem TaylorPolynomialTasteGate_single_carrier_alignment_fields :
    ∀ x y : TaylorPolynomialUp, taylorPolynomialFields x = taylorPolynomialFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk c1 k1 d1 j1 p1 v1 q1 e1 h1 r1 g1 n1 =>
      cases y with
      | mk c2 k2 d2 j2 p2 v2 q2 e2 h2 r2 g2 n2 =>
          cases hfields
          rfl

instance taylorPolynomialBHistCarrier : BHistCarrier TaylorPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := taylorPolynomialToEventFlow
  fromEventFlow := taylorPolynomialFromEventFlow

instance taylorPolynomialChapterTasteGate : ChapterTasteGate TaylorPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change taylorPolynomialFromEventFlow (taylorPolynomialToEventFlow x) = some x
    exact TaylorPolynomialTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (TaylorPolynomialTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance taylorPolynomialFieldFaithful : FieldFaithful TaylorPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := taylorPolynomialFields
  field_faithful := TaylorPolynomialTasteGate_single_carrier_alignment_fields

instance taylorPolynomialNontrivial : Nontrivial TaylorPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TaylorPolynomialUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      TaylorPolynomialUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TaylorPolynomialUp :=
  -- BEDC touchpoint anchor: BHist BMark
  taylorPolynomialChapterTasteGate

theorem TaylorPolynomialTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier TaylorPolynomialUp) ∧
      (∀ x : TaylorPolynomialUp,
        taylorPolynomialFromEventFlow (taylorPolynomialToEventFlow x) = some x) ∧
        (∀ x y : TaylorPolynomialUp,
          taylorPolynomialToEventFlow x = taylorPolynomialToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful TaylorPolynomialUp) ∧
            Nonempty (ChapterTasteGate TaylorPolynomialUp) ∧
              Nonempty (Nontrivial TaylorPolynomialUp) ∧
                taylorPolynomialEncodeBHist BHist.Empty = ([] : RawEvent) ∧
                  taylorPolynomialEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨⟨taylorPolynomialBHistCarrier⟩,
      TaylorPolynomialTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => TaylorPolynomialTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      ⟨taylorPolynomialFieldFaithful⟩,
      ⟨taylorPolynomialChapterTasteGate⟩,
      ⟨taylorPolynomialNontrivial⟩,
      rfl,
      rfl⟩

end BEDC.Derived.TaylorPolynomialUp
