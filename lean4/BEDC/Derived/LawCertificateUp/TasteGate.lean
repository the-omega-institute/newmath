import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LawCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LawCertificateUp : Type where
  | mk :
      (sourceFit pattern classifier stability failure ledger transport replay provenance
        name : BHist) →
        LawCertificateUp
  deriving DecidableEq

def lawCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lawCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lawCertificateEncodeBHist h

def lawCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lawCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lawCertificateDecodeBHist tail)

private theorem lawCertificateDecode_encode :
    ∀ h : BHist, lawCertificateDecodeBHist (lawCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def lawCertificateFields : LawCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LawCertificateUp.mk F P C S E Ld H R Q N => [F, P, C, S, E, Ld, H, R, Q, N]

def lawCertificateToEventFlow : LawCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LawCertificateUp.mk F P C S E Ld H R Q N =>
      [[BMark.b0],
        lawCertificateEncodeBHist F,
        [BMark.b1, BMark.b0],
        lawCertificateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b0],
        lawCertificateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawCertificateEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawCertificateEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawCertificateEncodeBHist Ld,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        lawCertificateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        lawCertificateEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        lawCertificateEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        lawCertificateEncodeBHist N]

private def lawCertificateEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => lawCertificateEventAtDefault index rest

def lawCertificateFromEventFlow (ef : EventFlow) : Option LawCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LawCertificateUp.mk
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 1 ef))
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 3 ef))
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 5 ef))
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 7 ef))
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 9 ef))
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 11 ef))
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 13 ef))
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 15 ef))
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 17 ef))
      (lawCertificateDecodeBHist (lawCertificateEventAtDefault 19 ef)))

private theorem lawCertificate_round_trip :
    ∀ x : LawCertificateUp,
      lawCertificateFromEventFlow (lawCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F P C S E Ld H R Q N =>
      change
        some
          (LawCertificateUp.mk
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist F))
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist P))
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist C))
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist S))
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist E))
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist Ld))
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist H))
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist R))
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist Q))
            (lawCertificateDecodeBHist (lawCertificateEncodeBHist N))) =
          some (LawCertificateUp.mk F P C S E Ld H R Q N)
      rw [lawCertificateDecode_encode F, lawCertificateDecode_encode P,
        lawCertificateDecode_encode C, lawCertificateDecode_encode S,
        lawCertificateDecode_encode E, lawCertificateDecode_encode Ld,
        lawCertificateDecode_encode H, lawCertificateDecode_encode R,
        lawCertificateDecode_encode Q, lawCertificateDecode_encode N]

private theorem lawCertificateToEventFlow_injective {x y : LawCertificateUp} :
    lawCertificateToEventFlow x = lawCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lawCertificateFromEventFlow (lawCertificateToEventFlow x) =
        lawCertificateFromEventFlow (lawCertificateToEventFlow y) :=
    congrArg lawCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (lawCertificate_round_trip x).symm
      (Eq.trans hread (lawCertificate_round_trip y)))

private theorem lawCertificate_fields_faithful :
    ∀ x y : LawCertificateUp, lawCertificateFields x = lawCertificateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F₁ P₁ C₁ S₁ E₁ Ld₁ H₁ R₁ Q₁ N₁ =>
      cases y with
      | mk F₂ P₂ C₂ S₂ E₂ Ld₂ H₂ R₂ Q₂ N₂ =>
          cases hfields
          rfl

instance lawCertificateBHistCarrier : BHistCarrier LawCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lawCertificateToEventFlow
  fromEventFlow := lawCertificateFromEventFlow

instance lawCertificateChapterTasteGate : ChapterTasteGate LawCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lawCertificateFromEventFlow (lawCertificateToEventFlow x) = some x
    exact lawCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (lawCertificateToEventFlow_injective heq)

instance lawCertificateFieldFaithful : FieldFaithful LawCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := lawCertificateFields
  field_faithful := lawCertificate_fields_faithful

instance lawCertificateNontrivial : Nontrivial LawCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LawCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LawCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LawCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  lawCertificateChapterTasteGate

end BEDC.Derived.LawCertificateUp
