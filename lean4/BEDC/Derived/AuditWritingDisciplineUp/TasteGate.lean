import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
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
      auditWritingDisciplineDecodeBHist
        (auditWritingDisciplineEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def auditWritingDisciplineFields :
    AuditWritingDisciplineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AuditWritingDisciplineUp.mk W C K L T F G R H P N =>
      [W, C, K, L, T, F, G, R, H, P, N]

def auditWritingDisciplineToEventFlow :
    AuditWritingDisciplineUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (auditWritingDisciplineFields x).map auditWritingDisciplineEncodeBHist

private def auditWritingDisciplineEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      auditWritingDisciplineEventAtDefault index rest

def auditWritingDisciplineFromEventFlow :
    EventFlow → Option AuditWritingDisciplineUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (AuditWritingDisciplineUp.mk
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 0 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 1 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 2 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 3 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 4 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 5 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 6 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 7 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 8 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 9 ef))
          (auditWritingDisciplineDecodeBHist
            (auditWritingDisciplineEventAtDefault 10 ef)))

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
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist W))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist C))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist K))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist L))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist T))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist F))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist G))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist R))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist H))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist P))
            (auditWritingDisciplineDecodeBHist
              (auditWritingDisciplineEncodeBHist N))) =
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
    auditWritingDisciplineToEventFlow x =
      auditWritingDisciplineToEventFlow y → x = y := by
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

private theorem auditWritingDiscipline_fields_faithful :
    ∀ x y : AuditWritingDisciplineUp,
      auditWritingDisciplineFields x =
        auditWritingDisciplineFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk W₁ C₁ K₁ L₁ T₁ F₁ G₁ R₁ H₁ P₁ N₁ =>
      cases y with
      | mk W₂ C₂ K₂ L₂ T₂ F₂ G₂ R₂ H₂ P₂ N₂ =>
          cases hfields
          rfl

instance auditWritingDisciplineBHistCarrier :
    BHistCarrier AuditWritingDisciplineUp where
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
  field_faithful := auditWritingDiscipline_fields_faithful

instance auditWritingDisciplineNontrivial :
    Nontrivial AuditWritingDisciplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AuditWritingDisciplineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      AuditWritingDisciplineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AuditWritingDisciplineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  auditWritingDisciplineChapterTasteGate

theorem AuditWritingDisciplineUp_single_carrier_alignment :
    (∀ h : BHist,
      auditWritingDisciplineDecodeBHist (auditWritingDisciplineEncodeBHist h) = h) ∧
      (∀ x : AuditWritingDisciplineUp,
        auditWritingDisciplineFromEventFlow
          (auditWritingDisciplineToEventFlow x) = some x) ∧
        (∀ x y : AuditWritingDisciplineUp,
          auditWritingDisciplineToEventFlow x =
            auditWritingDisciplineToEventFlow y -> x = y) ∧
          auditWritingDisciplineEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact auditWritingDisciplineDecode_encode_bhist
  · constructor
    · exact auditWritingDiscipline_round_trip
    · constructor
      · intro x y heq
        exact auditWritingDisciplineToEventFlow_injective heq
      · rfl

end BEDC.Derived.AuditWritingDisciplineUp
