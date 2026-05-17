import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditFinalityCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditFinalityCertificateUp : Type where
  | mk (K C F R E S W L H T P N : BHist) : AuditFinalityCertificateUp
  deriving DecidableEq

def auditFinalityCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditFinalityCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditFinalityCertificateEncodeBHist h

def auditFinalityCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditFinalityCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditFinalityCertificateDecodeBHist tail)

private theorem auditFinalityCertificate_decode_encode_bhist :
    ∀ h : BHist,
      auditFinalityCertificateDecodeBHist
        (auditFinalityCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def auditFinalityCertificateFields :
    AuditFinalityCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditFinalityCertificateUp.mk K C F R E S W L H T P N =>
      [K, C, F, R, E, S, W, L, H, T, P, N]

def auditFinalityCertificateToEventFlow :
    AuditFinalityCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditFinalityCertificateUp.mk K C F R E S W L H T P N =>
      [[BMark.b0],
        auditFinalityCertificateEncodeBHist K,
        [BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditFinalityCertificateEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditFinalityCertificateEncodeBHist N]

private def auditFinalityCertificateRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => auditFinalityCertificateRawAt n rest

private def auditFinalityCertificateLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => auditFinalityCertificateLengthEq n rest

def auditFinalityCertificateFromEventFlow :
    EventFlow → Option AuditFinalityCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match auditFinalityCertificateLengthEq 24 flow with
      | true =>
          some
            (AuditFinalityCertificateUp.mk
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 1 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 3 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 5 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 7 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 9 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 11 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 13 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 15 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 17 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 19 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 21 flow))
              (auditFinalityCertificateDecodeBHist
                (auditFinalityCertificateRawAt 23 flow)))
      | false => none

private theorem auditFinalityCertificate_round_trip :
    ∀ x : AuditFinalityCertificateUp,
      auditFinalityCertificateFromEventFlow
        (auditFinalityCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K C F R E S W L H T P N =>
      change
        some
          (AuditFinalityCertificateUp.mk
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist K))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist C))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist F))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist R))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist E))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist S))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist W))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist L))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist H))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist T))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist P))
            (auditFinalityCertificateDecodeBHist
              (auditFinalityCertificateEncodeBHist N))) =
          some (AuditFinalityCertificateUp.mk K C F R E S W L H T P N)
      rw [auditFinalityCertificate_decode_encode_bhist K,
        auditFinalityCertificate_decode_encode_bhist C,
        auditFinalityCertificate_decode_encode_bhist F,
        auditFinalityCertificate_decode_encode_bhist R,
        auditFinalityCertificate_decode_encode_bhist E,
        auditFinalityCertificate_decode_encode_bhist S,
        auditFinalityCertificate_decode_encode_bhist W,
        auditFinalityCertificate_decode_encode_bhist L,
        auditFinalityCertificate_decode_encode_bhist H,
        auditFinalityCertificate_decode_encode_bhist T,
        auditFinalityCertificate_decode_encode_bhist P,
        auditFinalityCertificate_decode_encode_bhist N]

private theorem auditFinalityCertificateToEventFlow_injective
    {x y : AuditFinalityCertificateUp} :
    auditFinalityCertificateToEventFlow x =
        auditFinalityCertificateToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditFinalityCertificateFromEventFlow
          (auditFinalityCertificateToEventFlow x) =
        auditFinalityCertificateFromEventFlow
          (auditFinalityCertificateToEventFlow y) :=
    congrArg auditFinalityCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditFinalityCertificate_round_trip x).symm
      (Eq.trans hread (auditFinalityCertificate_round_trip y)))

private theorem auditFinalityCertificate_field_faithful :
    ∀ x y : AuditFinalityCertificateUp,
      auditFinalityCertificateFields x =
          auditFinalityCertificateFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K1 C1 F1 R1 E1 S1 W1 L1 H1 T1 P1 N1 =>
      cases y with
      | mk K2 C2 F2 R2 E2 S2 W2 L2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance auditFinalityCertificateBHistCarrier :
    BHistCarrier AuditFinalityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditFinalityCertificateToEventFlow
  fromEventFlow := auditFinalityCertificateFromEventFlow

instance auditFinalityCertificateChapterTasteGate :
    ChapterTasteGate AuditFinalityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      auditFinalityCertificateFromEventFlow
          (auditFinalityCertificateToEventFlow x) = some x
    exact auditFinalityCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditFinalityCertificateToEventFlow_injective heq)

instance auditFinalityCertificateFieldFaithful :
    FieldFaithful AuditFinalityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditFinalityCertificateFields
  field_faithful := auditFinalityCertificate_field_faithful

instance auditFinalityCertificateNontrivial :
    Nontrivial AuditFinalityCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditFinalityCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      AuditFinalityCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditFinalityCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditFinalityCertificateChapterTasteGate

end BEDC.Derived.AuditFinalityCertificateUp
