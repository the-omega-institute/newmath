import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AuditMapCoverageLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AuditMapCoverageLedgerUp : Type where
  | mk (M E C O F X H R P N : BHist) : AuditMapCoverageLedgerUp

def auditMapCoverageLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: auditMapCoverageLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: auditMapCoverageLedgerEncodeBHist h

def auditMapCoverageLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (auditMapCoverageLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (auditMapCoverageLedgerDecodeBHist tail)

private theorem auditMapCoverageLedger_decode_encode_bhist :
    ∀ h : BHist,
      auditMapCoverageLedgerDecodeBHist
        (auditMapCoverageLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditMapCoverageLedgerFields :
    AuditMapCoverageLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapCoverageLedgerUp.mk M E C O F X H R P N => [M, E, C, O, F, X, H, R, P, N]

def auditMapCoverageLedgerToEventFlow :
    AuditMapCoverageLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | AuditMapCoverageLedgerUp.mk M E C O F X H R P N =>
      [auditMapCoverageLedgerEncodeBHist M,
        auditMapCoverageLedgerEncodeBHist E,
        auditMapCoverageLedgerEncodeBHist C,
        auditMapCoverageLedgerEncodeBHist O,
        auditMapCoverageLedgerEncodeBHist F,
        auditMapCoverageLedgerEncodeBHist X,
        auditMapCoverageLedgerEncodeBHist H,
        auditMapCoverageLedgerEncodeBHist R,
        auditMapCoverageLedgerEncodeBHist P,
        auditMapCoverageLedgerEncodeBHist N]

def auditMapCoverageLedgerFromEventFlow :
    EventFlow → Option AuditMapCoverageLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | M :: E :: C :: O :: F :: X :: H :: R :: P :: N :: [] =>
      some
        (AuditMapCoverageLedgerUp.mk
          (auditMapCoverageLedgerDecodeBHist M)
          (auditMapCoverageLedgerDecodeBHist E)
          (auditMapCoverageLedgerDecodeBHist C)
          (auditMapCoverageLedgerDecodeBHist O)
          (auditMapCoverageLedgerDecodeBHist F)
          (auditMapCoverageLedgerDecodeBHist X)
          (auditMapCoverageLedgerDecodeBHist H)
          (auditMapCoverageLedgerDecodeBHist R)
          (auditMapCoverageLedgerDecodeBHist P)
          (auditMapCoverageLedgerDecodeBHist N))
  | _ => none

private theorem auditMapCoverageLedger_round_trip :
    ∀ x : AuditMapCoverageLedgerUp,
      auditMapCoverageLedgerFromEventFlow
        (auditMapCoverageLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M E C O F X H R P N =>
      change
        some
            (AuditMapCoverageLedgerUp.mk
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist M))
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist E))
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist C))
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist O))
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist F))
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist X))
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist H))
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist R))
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist P))
              (auditMapCoverageLedgerDecodeBHist (auditMapCoverageLedgerEncodeBHist N))) =
          some (AuditMapCoverageLedgerUp.mk M E C O F X H R P N)
      rw [auditMapCoverageLedger_decode_encode_bhist M,
        auditMapCoverageLedger_decode_encode_bhist E,
        auditMapCoverageLedger_decode_encode_bhist C,
        auditMapCoverageLedger_decode_encode_bhist O,
        auditMapCoverageLedger_decode_encode_bhist F,
        auditMapCoverageLedger_decode_encode_bhist X,
        auditMapCoverageLedger_decode_encode_bhist H,
        auditMapCoverageLedger_decode_encode_bhist R,
        auditMapCoverageLedger_decode_encode_bhist P,
        auditMapCoverageLedger_decode_encode_bhist N]

private theorem auditMapCoverageLedgerToEventFlow_injective
    {x y : AuditMapCoverageLedgerUp}
    (h : auditMapCoverageLedgerToEventFlow x =
      auditMapCoverageLedgerToEventFlow y) :
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  have hread :
      auditMapCoverageLedgerFromEventFlow (auditMapCoverageLedgerToEventFlow x) =
        auditMapCoverageLedgerFromEventFlow (auditMapCoverageLedgerToEventFlow y) :=
    congrArg auditMapCoverageLedgerFromEventFlow h
  exact Option.some.inj
    (Eq.trans (auditMapCoverageLedger_round_trip x).symm
      (Eq.trans hread (auditMapCoverageLedger_round_trip y)))

private theorem auditMapCoverageLedger_fields_faithful :
    ∀ x y : AuditMapCoverageLedgerUp,
      auditMapCoverageLedgerFields x = auditMapCoverageLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk M E C O F X H R P N =>
      cases y with
      | mk M' E' C' O' F' X' H' R' P' N' =>
          cases hfields
          rfl

instance auditMapCoverageLedgerBHistCarrier :
    BHistCarrier AuditMapCoverageLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := auditMapCoverageLedgerToEventFlow
  fromEventFlow := auditMapCoverageLedgerFromEventFlow

instance auditMapCoverageLedgerChapterTasteGate :
    ChapterTasteGate AuditMapCoverageLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      auditMapCoverageLedgerFromEventFlow
        (auditMapCoverageLedgerToEventFlow x) = some x
    exact auditMapCoverageLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (auditMapCoverageLedgerToEventFlow_injective heq)

def taste_gate : ChapterTasteGate AuditMapCoverageLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditMapCoverageLedgerChapterTasteGate

theorem AuditMapCoverageLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      auditMapCoverageLedgerDecodeBHist
        (auditMapCoverageLedgerEncodeBHist h) = h) ∧
      (∀ x y : AuditMapCoverageLedgerUp,
        auditMapCoverageLedgerFields x =
          auditMapCoverageLedgerFields y → x = y) ∧
          auditMapCoverageLedgerFields
              (AuditMapCoverageLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty) =
            [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
              BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
            auditMapCoverageLedgerEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              auditMapCoverageLedgerEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
                auditMapCoverageLedgerEncodeBHist (BHist.e1 BHist.Empty) = [BMark.b1] := by
  -- BEDC touchpoint anchor: BHist BMark
  exact ⟨auditMapCoverageLedger_decode_encode_bhist,
    auditMapCoverageLedger_fields_faithful,
    rfl, rfl, rfl, rfl⟩

end BEDC.Derived.AuditMapCoverageLedgerUp
