import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BairePointwiseOscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BairePointwiseOscillationUp : Type where
  | mk (X F S Qm Qp Rm Rp B H C P N : BHist) : BairePointwiseOscillationUp
  deriving DecidableEq

def bairePointwiseOscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: bairePointwiseOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: bairePointwiseOscillationEncodeBHist h

def bairePointwiseOscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (bairePointwiseOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (bairePointwiseOscillationDecodeBHist tail)

private theorem bairePointwiseOscillation_decode_encode_bhist :
    ∀ h : BHist,
      bairePointwiseOscillationDecodeBHist
        (bairePointwiseOscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def bairePointwiseOscillationFields :
    BairePointwiseOscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BairePointwiseOscillationUp.mk X F S Qm Qp Rm Rp B H C P N =>
      [X, F, S, Qm, Qp, Rm, Rp, B, H, C, P, N]

def bairePointwiseOscillationToEventFlow :
    BairePointwiseOscillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (bairePointwiseOscillationFields x).map bairePointwiseOscillationEncodeBHist

private def bairePointwiseOscillationEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => bairePointwiseOscillationEventAt index rest

def bairePointwiseOscillationFromEventFlow :
    EventFlow → Option BairePointwiseOscillationUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (BairePointwiseOscillationUp.mk
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 0 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 1 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 2 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 3 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 4 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 5 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 6 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 7 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 8 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 9 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 10 ef))
          (bairePointwiseOscillationDecodeBHist (bairePointwiseOscillationEventAt 11 ef)))

private theorem bairePointwiseOscillation_round_trip :
    ∀ x : BairePointwiseOscillationUp,
      bairePointwiseOscillationFromEventFlow
        (bairePointwiseOscillationToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X F S Qm Qp Rm Rp B H C P N =>
      change
        some
          (BairePointwiseOscillationUp.mk
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist X))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist F))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist S))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist Qm))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist Qp))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist Rm))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist Rp))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist B))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist H))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist C))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist P))
            (bairePointwiseOscillationDecodeBHist
              (bairePointwiseOscillationEncodeBHist N))) =
          some (BairePointwiseOscillationUp.mk X F S Qm Qp Rm Rp B H C P N)
      rw [bairePointwiseOscillation_decode_encode_bhist X,
        bairePointwiseOscillation_decode_encode_bhist F,
        bairePointwiseOscillation_decode_encode_bhist S,
        bairePointwiseOscillation_decode_encode_bhist Qm,
        bairePointwiseOscillation_decode_encode_bhist Qp,
        bairePointwiseOscillation_decode_encode_bhist Rm,
        bairePointwiseOscillation_decode_encode_bhist Rp,
        bairePointwiseOscillation_decode_encode_bhist B,
        bairePointwiseOscillation_decode_encode_bhist H,
        bairePointwiseOscillation_decode_encode_bhist C,
        bairePointwiseOscillation_decode_encode_bhist P,
        bairePointwiseOscillation_decode_encode_bhist N]

private theorem bairePointwiseOscillationToEventFlow_injective
    {x y : BairePointwiseOscillationUp} :
    bairePointwiseOscillationToEventFlow x =
        bairePointwiseOscillationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      bairePointwiseOscillationFromEventFlow
          (bairePointwiseOscillationToEventFlow x) =
        bairePointwiseOscillationFromEventFlow
          (bairePointwiseOscillationToEventFlow y) :=
    congrArg bairePointwiseOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (bairePointwiseOscillation_round_trip x).symm
      (Eq.trans hread (bairePointwiseOscillation_round_trip y)))

private theorem bairePointwiseOscillation_field_faithful :
    ∀ x y : BairePointwiseOscillationUp,
      bairePointwiseOscillationFields x = bairePointwiseOscillationFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 F1 S1 Qm1 Qp1 Rm1 Rp1 B1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 F2 S2 Qm2 Qp2 Rm2 Rp2 B2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance bairePointwiseOscillationBHistCarrier :
    BHistCarrier BairePointwiseOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := bairePointwiseOscillationToEventFlow
  fromEventFlow := bairePointwiseOscillationFromEventFlow

instance bairePointwiseOscillationChapterTasteGate :
    ChapterTasteGate BairePointwiseOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      bairePointwiseOscillationFromEventFlow
        (bairePointwiseOscillationToEventFlow x) = some x
    exact bairePointwiseOscillation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (bairePointwiseOscillationToEventFlow_injective heq)

instance bairePointwiseOscillationFieldFaithful :
    FieldFaithful BairePointwiseOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := bairePointwiseOscillationFields
  field_faithful := bairePointwiseOscillation_field_faithful

instance bairePointwiseOscillationNontrivial :
    Nontrivial BairePointwiseOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BairePointwiseOscillationUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      BairePointwiseOscillationUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BairePointwiseOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  bairePointwiseOscillationChapterTasteGate

theorem BairePointwiseOscillationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      bairePointwiseOscillationDecodeBHist
        (bairePointwiseOscillationEncodeBHist h) = h) ∧
      (∀ x : BairePointwiseOscillationUp,
        bairePointwiseOscillationFromEventFlow
          (bairePointwiseOscillationToEventFlow x) = some x) ∧
        (∀ x y : BairePointwiseOscillationUp,
          bairePointwiseOscillationToEventFlow x =
              bairePointwiseOscillationToEventFlow y ->
            x = y) ∧
          bairePointwiseOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨bairePointwiseOscillation_decode_encode_bhist,
      bairePointwiseOscillation_round_trip,
      (fun _ _ heq => bairePointwiseOscillationToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.BairePointwiseOscillationUp
