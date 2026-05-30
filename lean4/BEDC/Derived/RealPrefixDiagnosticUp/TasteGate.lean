import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealPrefixDiagnosticUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealPrefixDiagnosticUp : Type where
  | mk (B W S R D E A H C P N : BHist) : RealPrefixDiagnosticUp
  deriving DecidableEq

def realPrefixDiagnosticEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realPrefixDiagnosticEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realPrefixDiagnosticEncodeBHist h

def realPrefixDiagnosticDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realPrefixDiagnosticDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realPrefixDiagnosticDecodeBHist tail)

private theorem RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realPrefixDiagnosticFields : RealPrefixDiagnosticUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealPrefixDiagnosticUp.mk B W S R D E A H C P N => [B, W, S, R, D, E, A, H, C, P, N]

def realPrefixDiagnosticToEventFlow : RealPrefixDiagnosticUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realPrefixDiagnosticFields x).map realPrefixDiagnosticEncodeBHist

private def realPrefixDiagnosticEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => realPrefixDiagnosticEventAt index rest

def realPrefixDiagnosticFromEventFlow (ef : EventFlow) : Option RealPrefixDiagnosticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RealPrefixDiagnosticUp.mk
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 0 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 1 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 2 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 3 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 4 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 5 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 6 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 7 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 8 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 9 ef))
      (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEventAt 10 ef)))

private theorem RealPrefixDiagnosticTasteGate_single_carrier_alignment_round_trip
    (x : RealPrefixDiagnosticUp) :
    realPrefixDiagnosticFromEventFlow (realPrefixDiagnosticToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B W S R D E A H C P N =>
      change
        some
          (RealPrefixDiagnosticUp.mk
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist B))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist W))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist S))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist R))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist D))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist E))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist A))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist H))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist C))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist P))
            (realPrefixDiagnosticDecodeBHist (realPrefixDiagnosticEncodeBHist N))) =
          some (RealPrefixDiagnosticUp.mk B W S R D E A H C P N)
      rw [RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode B,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode W,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode S,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode R,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode D,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode E,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode A,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode H,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode C,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode P,
        RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode N]

private theorem RealPrefixDiagnosticTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RealPrefixDiagnosticUp} :
    realPrefixDiagnosticToEventFlow x = realPrefixDiagnosticToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realPrefixDiagnosticFromEventFlow (realPrefixDiagnosticToEventFlow x) =
        realPrefixDiagnosticFromEventFlow (realPrefixDiagnosticToEventFlow y) :=
    congrArg realPrefixDiagnosticFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealPrefixDiagnosticTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealPrefixDiagnosticTasteGate_single_carrier_alignment_round_trip y)))

private theorem RealPrefixDiagnosticTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RealPrefixDiagnosticUp,
      realPrefixDiagnosticFields x = realPrefixDiagnosticFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B₁ W₁ S₁ R₁ D₁ E₁ A₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk B₂ W₂ S₂ R₂ D₂ E₂ A₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hB tail0
          injection tail0 with hW tail1
          injection tail1 with hS tail2
          injection tail2 with hR tail3
          injection tail3 with hD tail4
          injection tail4 with hE tail5
          injection tail5 with hA tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hB
          subst hW
          subst hS
          subst hR
          subst hD
          subst hE
          subst hA
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance realPrefixDiagnosticBHistCarrier : BHistCarrier RealPrefixDiagnosticUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realPrefixDiagnosticToEventFlow
  fromEventFlow := realPrefixDiagnosticFromEventFlow

instance realPrefixDiagnosticChapterTasteGate : ChapterTasteGate RealPrefixDiagnosticUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realPrefixDiagnosticFromEventFlow (realPrefixDiagnosticToEventFlow x) = some x
    exact RealPrefixDiagnosticTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealPrefixDiagnosticTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance realPrefixDiagnosticFieldFaithful : FieldFaithful RealPrefixDiagnosticUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realPrefixDiagnosticFields
  field_faithful := RealPrefixDiagnosticTasteGate_single_carrier_alignment_fields_faithful

instance realPrefixDiagnosticNontrivial : Nontrivial RealPrefixDiagnosticUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealPrefixDiagnosticUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealPrefixDiagnosticUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealPrefixDiagnosticUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realPrefixDiagnosticChapterTasteGate

theorem RealPrefixDiagnosticTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealPrefixDiagnosticUp) ∧
      Nonempty (FieldFaithful RealPrefixDiagnosticUp) ∧
        Nonempty (Nontrivial RealPrefixDiagnosticUp) ∧
          (∀ h : BHist, realPrefixDiagnosticDecodeBHist
            (realPrefixDiagnosticEncodeBHist h) = h) ∧
            (∀ x : RealPrefixDiagnosticUp,
              realPrefixDiagnosticFromEventFlow
                (realPrefixDiagnosticToEventFlow x) = some x) ∧
              realPrefixDiagnosticEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨realPrefixDiagnosticChapterTasteGate⟩,
      ⟨realPrefixDiagnosticFieldFaithful⟩,
      ⟨realPrefixDiagnosticNontrivial⟩,
      RealPrefixDiagnosticTasteGate_single_carrier_alignment_decode_encode,
      RealPrefixDiagnosticTasteGate_single_carrier_alignment_round_trip,
      rfl⟩

end BEDC.Derived.RealPrefixDiagnosticUp
