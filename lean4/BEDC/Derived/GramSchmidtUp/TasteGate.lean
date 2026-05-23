import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.GramSchmidtUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive GramSchmidtUp : Type where
  | mk (S O Z A R T H C P N : BHist) : GramSchmidtUp
  deriving DecidableEq

def gramSchmidtEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: gramSchmidtEncodeBHist h
  | BHist.e1 h => BMark.b1 :: gramSchmidtEncodeBHist h

def gramSchmidtDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (gramSchmidtDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (gramSchmidtDecodeBHist tail)

private theorem GramSchmidtTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, gramSchmidtDecodeBHist (gramSchmidtEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def gramSchmidtFields : GramSchmidtUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | GramSchmidtUp.mk S O Z A R T H C P N => [S, O, Z, A, R, T, H, C, P, N]

def gramSchmidtToEventFlow : GramSchmidtUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (gramSchmidtFields x).map gramSchmidtEncodeBHist

private def GramSchmidtTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      GramSchmidtTasteGate_single_carrier_alignment_eventAt index rest

def gramSchmidtFromEventFlow (ef : EventFlow) : Option GramSchmidtUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (GramSchmidtUp.mk
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 0 ef))
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 1 ef))
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 2 ef))
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 3 ef))
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 4 ef))
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 5 ef))
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 6 ef))
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 7 ef))
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 8 ef))
      (gramSchmidtDecodeBHist (GramSchmidtTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem GramSchmidtTasteGate_single_carrier_alignment_round_trip
    (x : GramSchmidtUp) :
    gramSchmidtFromEventFlow (gramSchmidtToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S O Z A R T H C P N =>
      change
        some
          (GramSchmidtUp.mk
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist S))
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist O))
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist Z))
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist A))
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist R))
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist T))
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist H))
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist C))
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist P))
            (gramSchmidtDecodeBHist (gramSchmidtEncodeBHist N))) =
          some (GramSchmidtUp.mk S O Z A R T H C P N)
      rw [GramSchmidtTasteGate_single_carrier_alignment_decode_encode S,
        GramSchmidtTasteGate_single_carrier_alignment_decode_encode O,
        GramSchmidtTasteGate_single_carrier_alignment_decode_encode Z,
        GramSchmidtTasteGate_single_carrier_alignment_decode_encode A,
        GramSchmidtTasteGate_single_carrier_alignment_decode_encode R,
        GramSchmidtTasteGate_single_carrier_alignment_decode_encode T,
        GramSchmidtTasteGate_single_carrier_alignment_decode_encode H,
        GramSchmidtTasteGate_single_carrier_alignment_decode_encode C,
        GramSchmidtTasteGate_single_carrier_alignment_decode_encode P,
        GramSchmidtTasteGate_single_carrier_alignment_decode_encode N]

private theorem GramSchmidtTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : GramSchmidtUp} :
    gramSchmidtToEventFlow x = gramSchmidtToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      gramSchmidtFromEventFlow (gramSchmidtToEventFlow x) =
        gramSchmidtFromEventFlow (gramSchmidtToEventFlow y) :=
    congrArg gramSchmidtFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (GramSchmidtTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (GramSchmidtTasteGate_single_carrier_alignment_round_trip y)))

private theorem GramSchmidtTasteGate_single_carrier_alignment_fields :
    ∀ x y : GramSchmidtUp, gramSchmidtFields x = gramSchmidtFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ O₁ Z₁ A₁ R₁ T₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ O₂ Z₂ A₂ R₂ T₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance gramSchmidtBHistCarrier : BHistCarrier GramSchmidtUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := gramSchmidtToEventFlow
  fromEventFlow := gramSchmidtFromEventFlow

instance gramSchmidtChapterTasteGate : ChapterTasteGate GramSchmidtUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change gramSchmidtFromEventFlow (gramSchmidtToEventFlow x) = some x
    exact GramSchmidtTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (GramSchmidtTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance gramSchmidtFieldFaithful : FieldFaithful GramSchmidtUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := gramSchmidtFields
  field_faithful := GramSchmidtTasteGate_single_carrier_alignment_fields

instance gramSchmidtNontrivial :
    BEDC.Meta.TasteGate.Nontrivial GramSchmidtUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨GramSchmidtUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      GramSchmidtUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def gramSchmidtTasteGate : ChapterTasteGate GramSchmidtUp :=
  -- BEDC touchpoint anchor: BHist BMark
  gramSchmidtChapterTasteGate

theorem GramSchmidtTasteGate_single_carrier_alignment :
    (∀ h : BHist, gramSchmidtDecodeBHist (gramSchmidtEncodeBHist h) = h) ∧
      (∀ x : GramSchmidtUp,
        gramSchmidtFromEventFlow (gramSchmidtToEventFlow x) = some x) ∧
        (∀ x y : GramSchmidtUp,
          gramSchmidtToEventFlow x = gramSchmidtToEventFlow y → x = y) ∧
          gramSchmidtEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : GramSchmidtUp, gramSchmidtFields x = gramSchmidtFields y → x = y) ∧
              (∃ x y : GramSchmidtUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨GramSchmidtTasteGate_single_carrier_alignment_decode_encode,
      GramSchmidtTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => GramSchmidtTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      GramSchmidtTasteGate_single_carrier_alignment_fields,
      ⟨GramSchmidtUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        GramSchmidtUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

end BEDC.Derived.GramSchmidtUp
