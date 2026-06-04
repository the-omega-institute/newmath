import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICTypedNormalizationAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICTypedNormalizationAuditUp : Type where
  | core (T K S P R Q F H C G N : BHist) : MetaCICTypedNormalizationAuditUp
  deriving DecidableEq

namespace MetaCICTypedNormalizationAuditUp

def mk (T K S P R Q F H C G N : BHist) : MetaCICTypedNormalizationAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  core T K S P R Q F H C G N

end MetaCICTypedNormalizationAuditUp

def metaCICTypedNormalizationAuditFields :
    MetaCICTypedNormalizationAuditUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICTypedNormalizationAuditUp.core T K S P R Q F H C G N =>
      [T, K, S, P, R, Q, F, H, C, G, N]

def metaCICTypedNormalizationAuditEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICTypedNormalizationAuditEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICTypedNormalizationAuditEncodeBHist h

def metaCICTypedNormalizationAuditDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICTypedNormalizationAuditDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICTypedNormalizationAuditDecodeBHist tail)

private theorem metaCICTypedNormalizationAuditDecode_encode_bhist :
    ∀ h : BHist,
      metaCICTypedNormalizationAuditDecodeBHist
        (metaCICTypedNormalizationAuditEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICTypedNormalizationAuditToEventFlow :
    MetaCICTypedNormalizationAuditUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICTypedNormalizationAuditFields x).map
      metaCICTypedNormalizationAuditEncodeBHist

def metaCICTypedNormalizationAuditFromEventFlow :
    EventFlow → Option MetaCICTypedNormalizationAuditUp
  -- BEDC touchpoint anchor: BHist BMark
  | T :: K :: S :: P :: R :: Q :: F :: H :: C :: G :: N :: [] =>
      some
        (MetaCICTypedNormalizationAuditUp.core
          (metaCICTypedNormalizationAuditDecodeBHist T)
          (metaCICTypedNormalizationAuditDecodeBHist K)
          (metaCICTypedNormalizationAuditDecodeBHist S)
          (metaCICTypedNormalizationAuditDecodeBHist P)
          (metaCICTypedNormalizationAuditDecodeBHist R)
          (metaCICTypedNormalizationAuditDecodeBHist Q)
          (metaCICTypedNormalizationAuditDecodeBHist F)
          (metaCICTypedNormalizationAuditDecodeBHist H)
          (metaCICTypedNormalizationAuditDecodeBHist C)
          (metaCICTypedNormalizationAuditDecodeBHist G)
          (metaCICTypedNormalizationAuditDecodeBHist N))
  | _ => none

private theorem metaCICTypedNormalizationAudit_round_trip :
    ∀ x : MetaCICTypedNormalizationAuditUp,
      metaCICTypedNormalizationAuditFromEventFlow
        (metaCICTypedNormalizationAuditToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | core T K S P R Q F H C G N =>
      change
        some
          (MetaCICTypedNormalizationAuditUp.core
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist T))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist K))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist S))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist P))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist R))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist Q))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist F))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist H))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist C))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist G))
            (metaCICTypedNormalizationAuditDecodeBHist
              (metaCICTypedNormalizationAuditEncodeBHist N))) =
          some (MetaCICTypedNormalizationAuditUp.core T K S P R Q F H C G N)
      rw [metaCICTypedNormalizationAuditDecode_encode_bhist T,
        metaCICTypedNormalizationAuditDecode_encode_bhist K,
        metaCICTypedNormalizationAuditDecode_encode_bhist S,
        metaCICTypedNormalizationAuditDecode_encode_bhist P,
        metaCICTypedNormalizationAuditDecode_encode_bhist R,
        metaCICTypedNormalizationAuditDecode_encode_bhist Q,
        metaCICTypedNormalizationAuditDecode_encode_bhist F,
        metaCICTypedNormalizationAuditDecode_encode_bhist H,
        metaCICTypedNormalizationAuditDecode_encode_bhist C,
        metaCICTypedNormalizationAuditDecode_encode_bhist G,
        metaCICTypedNormalizationAuditDecode_encode_bhist N]

private theorem metaCICTypedNormalizationAuditToEventFlow_injective
    {x y : MetaCICTypedNormalizationAuditUp} :
    metaCICTypedNormalizationAuditToEventFlow x =
      metaCICTypedNormalizationAuditToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICTypedNormalizationAuditFromEventFlow
          (metaCICTypedNormalizationAuditToEventFlow x) =
        metaCICTypedNormalizationAuditFromEventFlow
          (metaCICTypedNormalizationAuditToEventFlow y) :=
    congrArg metaCICTypedNormalizationAuditFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICTypedNormalizationAudit_round_trip x).symm
      (Eq.trans hread (metaCICTypedNormalizationAudit_round_trip y)))

private theorem metaCICTypedNormalizationAudit_fields_faithful :
    ∀ x y : MetaCICTypedNormalizationAuditUp,
      metaCICTypedNormalizationAuditFields x =
        metaCICTypedNormalizationAuditFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  exact metaCICTypedNormalizationAuditToEventFlow_injective
    (congrArg (List.map metaCICTypedNormalizationAuditEncodeBHist) hfields)

instance metaCICTypedNormalizationAuditBHistCarrier :
    BHistCarrier MetaCICTypedNormalizationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICTypedNormalizationAuditToEventFlow
  fromEventFlow := metaCICTypedNormalizationAuditFromEventFlow

instance metaCICTypedNormalizationAuditChapterTasteGate :
    ChapterTasteGate MetaCICTypedNormalizationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICTypedNormalizationAuditFromEventFlow
        (metaCICTypedNormalizationAuditToEventFlow x) = some x
    exact metaCICTypedNormalizationAudit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICTypedNormalizationAuditToEventFlow_injective heq)

instance metaCICTypedNormalizationAuditFieldFaithful :
    FieldFaithful MetaCICTypedNormalizationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICTypedNormalizationAuditFields
  field_faithful := metaCICTypedNormalizationAudit_fields_faithful

instance metaCICTypedNormalizationAuditNontrivial :
    Nontrivial MetaCICTypedNormalizationAuditUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICTypedNormalizationAuditUp.core BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICTypedNormalizationAuditUp.core (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICTypedNormalizationAuditUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICTypedNormalizationAuditChapterTasteGate

theorem MetaCICTypedNormalizationAuditNameCertObligations [AskSetup] [PackageSetup]
    (x : MetaCICTypedNormalizationAuditUp) :
    ∃ T K S P R Q F H C G N : BHist,
      x = MetaCICTypedNormalizationAuditUp.mk T K S P R Q F H C G N ∧
        metaCICTypedNormalizationAuditFields x = [T, K, S, P, R, Q, F, H, C, G, N] ∧
          (UnaryHistory N →
            SemanticNameCert
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row T ∨ hsame row K ∨ hsame row S ∨ hsame row P ∨ hsame row R ∨
                  hsame row Q ∨ hsame row F ∨ hsame row N)
              (fun row : BHist => hsame row N ∧ UnaryHistory row)
              hsame) := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert AskSetup PackageSetup
  cases x with
  | core T K S P R Q F H C G N =>
      refine ⟨T, K, S, P, R, Q, F, H, C, G, N, rfl, rfl, ?_⟩
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
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
        ledger_sound := by
          intro _row source
          exact source
      }

end BEDC.Derived.MetaCICTypedNormalizationAuditUp
