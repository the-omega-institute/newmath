import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditWritingDisciplineUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditWritingDisciplineUp : Type where
  | mk (W C K L T F G R H P N : BHist) : AuditWritingDisciplineUp
  deriving DecidableEq

def auditWritingDisciplineEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditWritingDisciplineEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditWritingDisciplineEncodeBHist h

def auditWritingDisciplineDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditWritingDisciplineDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditWritingDisciplineDecodeBHist tail)

private theorem auditWritingDisciplineDecode_encode_bhist :
    ∀ h : BHist,
      auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def auditWritingDisciplineFields : AuditWritingDisciplineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditWritingDisciplineUp.mk W C K L T F G R H P N => [W, C, K, L, T, F, G, R, H, P, N]

def auditWritingDisciplineToEventFlow : AuditWritingDisciplineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditWritingDisciplineUp.mk W C K L T F G R H P N =>
      [[BMark.b0],
        auditWritingDisciplineEncodeBHist W,
        [BMark.b1, BMark.b0],
        auditWritingDisciplineEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b0],
        auditWritingDisciplineEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditWritingDisciplineEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditWritingDisciplineEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditWritingDisciplineEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditWritingDisciplineEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        auditWritingDisciplineEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        auditWritingDisciplineEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        auditWritingDisciplineEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        auditWritingDisciplineEncodeBHist N]

private def auditWritingDisciplineRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => auditWritingDisciplineRawAt n rest

private def auditWritingDisciplineLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => auditWritingDisciplineLengthEq n rest

def auditWritingDisciplineFromEventFlow : EventFlow → Option AuditWritingDisciplineUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match auditWritingDisciplineLengthEq 22 flow with
      | true =>
          some
            (AuditWritingDisciplineUp.mk
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 1 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 3 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 5 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 7 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 9 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 11 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 13 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 15 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 17 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 19 flow))
              (auditWritingDisciplineDecodeBHist (auditWritingDisciplineRawAt 21 flow)))
      | false => none

private theorem auditWritingDiscipline_round_trip :
    ∀ x : AuditWritingDisciplineUp,
      auditWritingDisciplineFromEventFlow
        (auditWritingDisciplineToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk W C K L T F G R H P N =>
      change
        some
          (AuditWritingDisciplineUp.mk
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist W))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist C))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist K))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist L))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist T))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist F))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist G))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist R))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist H))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist P))
            (auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist N))) =
          some (AuditWritingDisciplineUp.mk W C K L T F G R H P N)
      rw [auditWritingDisciplineDecode_encode_bhist W,
        auditWritingDisciplineDecode_encode_bhist C,
        auditWritingDisciplineDecode_encode_bhist K,
        auditWritingDisciplineDecode_encode_bhist L,
        auditWritingDisciplineDecode_encode_bhist T,
        auditWritingDisciplineDecode_encode_bhist F,
        auditWritingDisciplineDecode_encode_bhist G,
        auditWritingDisciplineDecode_encode_bhist R,
        auditWritingDisciplineDecode_encode_bhist H,
        auditWritingDisciplineDecode_encode_bhist P,
        auditWritingDisciplineDecode_encode_bhist N]

private theorem auditWritingDisciplineToEventFlow_injective
    {x y : AuditWritingDisciplineUp} :
    auditWritingDisciplineToEventFlow x = auditWritingDisciplineToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      auditWritingDisciplineFromEventFlow
          (auditWritingDisciplineToEventFlow x) =
        auditWritingDisciplineFromEventFlow
          (auditWritingDisciplineToEventFlow y) :=
    congrArg auditWritingDisciplineFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (auditWritingDiscipline_round_trip x).symm
      (Eq.trans hread (auditWritingDiscipline_round_trip y)))

private theorem auditWritingDiscipline_field_faithful :
    ∀ x y : AuditWritingDisciplineUp,
      auditWritingDisciplineFields x = auditWritingDisciplineFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W1 C1 K1 L1 T1 F1 G1 R1 H1 P1 N1 =>
      cases y with
      | mk W2 C2 K2 L2 T2 F2 G2 R2 H2 P2 N2 =>
          cases hfields
          rfl

instance auditWritingDisciplineBHistCarrier : BHistCarrier AuditWritingDisciplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditWritingDisciplineToEventFlow
  fromEventFlow := auditWritingDisciplineFromEventFlow

instance auditWritingDisciplineChapterTasteGate :
    ChapterTasteGate AuditWritingDisciplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      auditWritingDisciplineFromEventFlow
        (auditWritingDisciplineToEventFlow x) = some x
    exact auditWritingDiscipline_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditWritingDisciplineToEventFlow_injective heq)

instance auditWritingDisciplineFieldFaithful :
    FieldFaithful AuditWritingDisciplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := auditWritingDisciplineFields
  field_faithful := auditWritingDiscipline_field_faithful

instance auditWritingDisciplineNontrivial : Nontrivial AuditWritingDisciplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditWritingDisciplineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AuditWritingDisciplineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditWritingDisciplineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditWritingDisciplineChapterTasteGate

theorem AuditWritingDisciplineTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist h) = h) ∧
      Nonempty (Nontrivial AuditWritingDisciplineUp) ∧
        Nonempty (ChapterTasteGate AuditWritingDisciplineUp) ∧
          Nonempty (FieldFaithful AuditWritingDisciplineUp) ∧
            auditWritingDisciplineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial ChapterTasteGate
  exact
    ⟨auditWritingDisciplineDecode_encode_bhist,
      ⟨auditWritingDisciplineNontrivial⟩,
      ⟨auditWritingDisciplineChapterTasteGate⟩,
      ⟨auditWritingDisciplineFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.AuditWritingDisciplineUp
