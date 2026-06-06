import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReassignmentSupportCompressionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReassignmentSupportCompressionUp : Type where
  | core (S M I U H C P N : BHist) : ReassignmentSupportCompressionUp
  deriving DecidableEq

namespace ReassignmentSupportCompressionUp

def mk (S M I U H C P N : BHist) : ReassignmentSupportCompressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  core S M I U H C P N

end ReassignmentSupportCompressionUp

def reassignmentSupportCompressionFields :
    ReassignmentSupportCompressionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ReassignmentSupportCompressionUp.core S M I U H C P N => [S, M, I, U, H, C, P, N]

def reassignmentSupportCompressionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reassignmentSupportCompressionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reassignmentSupportCompressionEncodeBHist h

def reassignmentSupportCompressionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reassignmentSupportCompressionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reassignmentSupportCompressionDecodeBHist tail)

private theorem reassignmentSupportCompressionDecode_encode_bhist :
    ∀ h : BHist,
      reassignmentSupportCompressionDecodeBHist
        (reassignmentSupportCompressionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def reassignmentSupportCompressionToEventFlow :
    ReassignmentSupportCompressionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (reassignmentSupportCompressionFields x).map
      reassignmentSupportCompressionEncodeBHist

def reassignmentSupportCompressionFromEventFlow :
    EventFlow → Option ReassignmentSupportCompressionUp
  -- BEDC touchpoint anchor: BHist BMark
  | S :: M :: I :: U :: H :: C :: P :: N :: [] =>
      some
        (ReassignmentSupportCompressionUp.core
          (reassignmentSupportCompressionDecodeBHist S)
          (reassignmentSupportCompressionDecodeBHist M)
          (reassignmentSupportCompressionDecodeBHist I)
          (reassignmentSupportCompressionDecodeBHist U)
          (reassignmentSupportCompressionDecodeBHist H)
          (reassignmentSupportCompressionDecodeBHist C)
          (reassignmentSupportCompressionDecodeBHist P)
          (reassignmentSupportCompressionDecodeBHist N))
  | _ => none

private theorem reassignmentSupportCompression_round_trip :
    ∀ x : ReassignmentSupportCompressionUp,
      reassignmentSupportCompressionFromEventFlow
        (reassignmentSupportCompressionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | core S M I U H C P N =>
      change
        some
          (ReassignmentSupportCompressionUp.core
            (reassignmentSupportCompressionDecodeBHist
              (reassignmentSupportCompressionEncodeBHist S))
            (reassignmentSupportCompressionDecodeBHist
              (reassignmentSupportCompressionEncodeBHist M))
            (reassignmentSupportCompressionDecodeBHist
              (reassignmentSupportCompressionEncodeBHist I))
            (reassignmentSupportCompressionDecodeBHist
              (reassignmentSupportCompressionEncodeBHist U))
            (reassignmentSupportCompressionDecodeBHist
              (reassignmentSupportCompressionEncodeBHist H))
            (reassignmentSupportCompressionDecodeBHist
              (reassignmentSupportCompressionEncodeBHist C))
            (reassignmentSupportCompressionDecodeBHist
              (reassignmentSupportCompressionEncodeBHist P))
            (reassignmentSupportCompressionDecodeBHist
              (reassignmentSupportCompressionEncodeBHist N))) =
          some (ReassignmentSupportCompressionUp.core S M I U H C P N)
      rw [reassignmentSupportCompressionDecode_encode_bhist S,
        reassignmentSupportCompressionDecode_encode_bhist M,
        reassignmentSupportCompressionDecode_encode_bhist I,
        reassignmentSupportCompressionDecode_encode_bhist U,
        reassignmentSupportCompressionDecode_encode_bhist H,
        reassignmentSupportCompressionDecode_encode_bhist C,
        reassignmentSupportCompressionDecode_encode_bhist P,
        reassignmentSupportCompressionDecode_encode_bhist N]

private theorem reassignmentSupportCompressionToEventFlow_injective
    {x y : ReassignmentSupportCompressionUp} :
    reassignmentSupportCompressionToEventFlow x =
      reassignmentSupportCompressionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reassignmentSupportCompressionFromEventFlow
          (reassignmentSupportCompressionToEventFlow x) =
        reassignmentSupportCompressionFromEventFlow
          (reassignmentSupportCompressionToEventFlow y) :=
    congrArg reassignmentSupportCompressionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (reassignmentSupportCompression_round_trip x).symm
      (Eq.trans hread (reassignmentSupportCompression_round_trip y)))

private theorem reassignmentSupportCompression_fields_faithful :
    ∀ x y : ReassignmentSupportCompressionUp,
      reassignmentSupportCompressionFields x =
        reassignmentSupportCompressionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  exact reassignmentSupportCompressionToEventFlow_injective
    (congrArg (List.map reassignmentSupportCompressionEncodeBHist) hfields)

instance reassignmentSupportCompressionBHistCarrier :
    BHistCarrier ReassignmentSupportCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reassignmentSupportCompressionToEventFlow
  fromEventFlow := reassignmentSupportCompressionFromEventFlow

instance reassignmentSupportCompressionChapterTasteGate :
    ChapterTasteGate ReassignmentSupportCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      reassignmentSupportCompressionFromEventFlow
        (reassignmentSupportCompressionToEventFlow x) = some x
    exact reassignmentSupportCompression_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (reassignmentSupportCompressionToEventFlow_injective heq)

instance reassignmentSupportCompressionFieldFaithful :
    FieldFaithful ReassignmentSupportCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := reassignmentSupportCompressionFields
  field_faithful := reassignmentSupportCompression_fields_faithful

instance reassignmentSupportCompressionNontrivial :
    Nontrivial ReassignmentSupportCompressionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ReassignmentSupportCompressionUp.core BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ReassignmentSupportCompressionUp.core (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ReassignmentSupportCompressionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  reassignmentSupportCompressionChapterTasteGate

theorem ReassignmentSupportCompressionNameCertObligations [AskSetup] [PackageSetup]
    (x : ReassignmentSupportCompressionUp) :
    ∃ S M I U H C P N : BHist,
      x = ReassignmentSupportCompressionUp.mk S M I U H C P N ∧
        reassignmentSupportCompressionFields x = [S, M, I, U, H, C, P, N] ∧
          (UnaryHistory N →
            SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row S ∨ hsame row M ∨ hsame row I ∨ hsame row U ∨ hsame row N)
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              hsame) := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert AskSetup PackageSetup
  cases x with
  | core S M I U H C P N =>
      refine ⟨S, M, I, U, H, C, P, N, rfl, rfl, ?_⟩
      intro nUnary
      exact {
        core := {
          carrier_inhabited := Exists.intro N (And.intro (hsame_refl N) nUnary)
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro row col same
            exact hsame_symm same
          equiv_trans := by
            intro row col next sameRowCol sameColNext
            exact hsame_trans sameRowCol sameColNext
          carrier_respects_equiv := by
            intro row col same source
            exact And.intro (hsame_trans (hsame_symm same) source.left) (by
              cases same
              exact source.right)
        }
        pattern_sound := by
          intro _row source
          exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.ReassignmentSupportCompressionUp
