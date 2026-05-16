import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PhysicalTruthCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PhysicalTruthCertificateUp : Type where
  | mk (S F O D I L R H C P N : BHist) : PhysicalTruthCertificateUp
  deriving DecidableEq

def physicalTruthCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: physicalTruthCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: physicalTruthCertificateEncodeBHist h

def physicalTruthCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (physicalTruthCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (physicalTruthCertificateDecodeBHist tail)

private theorem physicalTruthCertificateDecode_encode_bhist :
    ∀ h : BHist,
      physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def physicalTruthCertificateFields : PhysicalTruthCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalTruthCertificateUp.mk S F O D I L R H C P N => [S, F, O, D, I, L, R, H, C, P, N]

def physicalTruthCertificateToEventFlow : PhysicalTruthCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PhysicalTruthCertificateUp.mk S F O D I L R H C P N =>
      [[BMark.b0],
        physicalTruthCertificateEncodeBHist S,
        [BMark.b1, BMark.b0],
        physicalTruthCertificateEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        physicalTruthCertificateEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalTruthCertificateEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalTruthCertificateEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalTruthCertificateEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalTruthCertificateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        physicalTruthCertificateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        physicalTruthCertificateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        physicalTruthCertificateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        physicalTruthCertificateEncodeBHist N]

private def physicalTruthCertificateRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => physicalTruthCertificateRawAt n rest

private def physicalTruthCertificateLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => physicalTruthCertificateLengthEq n rest

def physicalTruthCertificateFromEventFlow : EventFlow → Option PhysicalTruthCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match physicalTruthCertificateLengthEq 22 flow with
      | true =>
          some
            (PhysicalTruthCertificateUp.mk
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 1 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 3 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 5 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 7 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 9 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 11 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 13 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 15 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 17 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 19 flow))
              (physicalTruthCertificateDecodeBHist (physicalTruthCertificateRawAt 21 flow)))
      | false => none

private theorem physicalTruthCertificate_round_trip :
    ∀ x : PhysicalTruthCertificateUp,
      physicalTruthCertificateFromEventFlow
        (physicalTruthCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S F O D I L R H C P N =>
      change
        some
          (PhysicalTruthCertificateUp.mk
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist S))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist F))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist O))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist D))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist I))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist L))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist R))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist H))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist C))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist P))
            (physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist N))) =
          some (PhysicalTruthCertificateUp.mk S F O D I L R H C P N)
      rw [physicalTruthCertificateDecode_encode_bhist S,
        physicalTruthCertificateDecode_encode_bhist F,
        physicalTruthCertificateDecode_encode_bhist O,
        physicalTruthCertificateDecode_encode_bhist D,
        physicalTruthCertificateDecode_encode_bhist I,
        physicalTruthCertificateDecode_encode_bhist L,
        physicalTruthCertificateDecode_encode_bhist R,
        physicalTruthCertificateDecode_encode_bhist H,
        physicalTruthCertificateDecode_encode_bhist C,
        physicalTruthCertificateDecode_encode_bhist P,
        physicalTruthCertificateDecode_encode_bhist N]

private theorem physicalTruthCertificateToEventFlow_injective
    {x y : PhysicalTruthCertificateUp} :
    physicalTruthCertificateToEventFlow x =
        physicalTruthCertificateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      physicalTruthCertificateFromEventFlow
          (physicalTruthCertificateToEventFlow x) =
        physicalTruthCertificateFromEventFlow
          (physicalTruthCertificateToEventFlow y) :=
    congrArg physicalTruthCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (physicalTruthCertificate_round_trip x).symm
      (Eq.trans hread (physicalTruthCertificate_round_trip y)))

private theorem physicalTruthCertificate_field_faithful :
    ∀ x y : PhysicalTruthCertificateUp,
      physicalTruthCertificateFields x = physicalTruthCertificateFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 F1 O1 D1 I1 L1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 F2 O2 D2 I2 L2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance physicalTruthCertificateBHistCarrier : BHistCarrier PhysicalTruthCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := physicalTruthCertificateToEventFlow
  fromEventFlow := physicalTruthCertificateFromEventFlow

instance physicalTruthCertificateChapterTasteGate :
    ChapterTasteGate PhysicalTruthCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      physicalTruthCertificateFromEventFlow
        (physicalTruthCertificateToEventFlow x) = some x
    exact physicalTruthCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (physicalTruthCertificateToEventFlow_injective heq)

instance physicalTruthCertificateFieldFaithful :
    FieldFaithful PhysicalTruthCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := physicalTruthCertificateFields
  field_faithful := physicalTruthCertificate_field_faithful

instance physicalTruthCertificateNontrivial : Nontrivial PhysicalTruthCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PhysicalTruthCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      PhysicalTruthCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PhysicalTruthCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  physicalTruthCertificateChapterTasteGate

theorem PhysicalTruthCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist, physicalTruthCertificateDecodeBHist (physicalTruthCertificateEncodeBHist h) = h) ∧
      (∀ x : PhysicalTruthCertificateUp,
        physicalTruthCertificateFromEventFlow (physicalTruthCertificateToEventFlow x) = some x) ∧
        (∀ x y : PhysicalTruthCertificateUp,
          physicalTruthCertificateToEventFlow x = physicalTruthCertificateToEventFlow y → x = y) ∧
          physicalTruthCertificateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨physicalTruthCertificateDecode_encode_bhist,
      physicalTruthCertificate_round_trip,
      (fun _ _ heq => physicalTruthCertificateToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.PhysicalTruthCertificateUp
