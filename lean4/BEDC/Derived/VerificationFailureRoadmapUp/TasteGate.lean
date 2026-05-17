import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.VerificationFailureRoadmapUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive VerificationFailureRoadmapUp : Type where
  | mk : (R A F D M U B T C P N : BHist) → VerificationFailureRoadmapUp
  deriving DecidableEq

def verificationFailureRoadmapFields : VerificationFailureRoadmapUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | VerificationFailureRoadmapUp.mk R A F D M U B T C P N =>
      [R, A, F, D, M, U, B, T, C, P, N]

private def verificationFailureRoadmapEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: verificationFailureRoadmapEncodeBHist h
  | BHist.e1 h => BMark.b1 :: verificationFailureRoadmapEncodeBHist h

private def verificationFailureRoadmapDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (verificationFailureRoadmapDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (verificationFailureRoadmapDecodeBHist tail)

private theorem verificationFailureRoadmapDecode_encode_bhist :
    ∀ h : BHist,
      verificationFailureRoadmapDecodeBHist
        (verificationFailureRoadmapEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def verificationFailureRoadmapToEventFlow :
    VerificationFailureRoadmapUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (verificationFailureRoadmapFields x).map verificationFailureRoadmapEncodeBHist

private def verificationFailureRoadmapEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      verificationFailureRoadmapEventAtDefault index rest

def verificationFailureRoadmapFromEventFlow :
    EventFlow → Option VerificationFailureRoadmapUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (VerificationFailureRoadmapUp.mk
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 0 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 1 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 2 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 3 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 4 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 5 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 6 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 7 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 8 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 9 ef))
          (verificationFailureRoadmapDecodeBHist
            (verificationFailureRoadmapEventAtDefault 10 ef)))

private theorem verificationFailureRoadmap_round_trip :
    ∀ x : VerificationFailureRoadmapUp,
      verificationFailureRoadmapFromEventFlow
        (verificationFailureRoadmapToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R A F D M U B T C P N =>
      change
        some
          (VerificationFailureRoadmapUp.mk
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist R))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist A))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist F))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist D))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist M))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist U))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist B))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist T))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist C))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist P))
            (verificationFailureRoadmapDecodeBHist (verificationFailureRoadmapEncodeBHist N))) =
          some (VerificationFailureRoadmapUp.mk R A F D M U B T C P N)
      rw [verificationFailureRoadmapDecode_encode_bhist R,
        verificationFailureRoadmapDecode_encode_bhist A,
        verificationFailureRoadmapDecode_encode_bhist F,
        verificationFailureRoadmapDecode_encode_bhist D,
        verificationFailureRoadmapDecode_encode_bhist M,
        verificationFailureRoadmapDecode_encode_bhist U,
        verificationFailureRoadmapDecode_encode_bhist B,
        verificationFailureRoadmapDecode_encode_bhist T,
        verificationFailureRoadmapDecode_encode_bhist C,
        verificationFailureRoadmapDecode_encode_bhist P,
        verificationFailureRoadmapDecode_encode_bhist N]

private theorem verificationFailureRoadmapToEventFlow_injective
    {x y : VerificationFailureRoadmapUp} :
    verificationFailureRoadmapToEventFlow x =
      verificationFailureRoadmapToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      verificationFailureRoadmapFromEventFlow
          (verificationFailureRoadmapToEventFlow x) =
        verificationFailureRoadmapFromEventFlow
          (verificationFailureRoadmapToEventFlow y) :=
    congrArg verificationFailureRoadmapFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (verificationFailureRoadmap_round_trip x).symm
      (Eq.trans hread (verificationFailureRoadmap_round_trip y)))

private theorem verificationFailureRoadmap_fields_faithful :
    ∀ x y : VerificationFailureRoadmapUp,
      verificationFailureRoadmapFields x =
        verificationFailureRoadmapFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R₁ A₁ F₁ D₁ M₁ U₁ B₁ T₁ C₁ P₁ N₁ =>
      cases y with
      | mk R₂ A₂ F₂ D₂ M₂ U₂ B₂ T₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance verificationFailureRoadmapBHistCarrier :
    BHistCarrier VerificationFailureRoadmapUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := verificationFailureRoadmapToEventFlow
  fromEventFlow := verificationFailureRoadmapFromEventFlow

instance verificationFailureRoadmapChapterTasteGate :
    ChapterTasteGate VerificationFailureRoadmapUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      verificationFailureRoadmapFromEventFlow
        (verificationFailureRoadmapToEventFlow x) = some x
    exact verificationFailureRoadmap_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (verificationFailureRoadmapToEventFlow_injective heq)

instance verificationFailureRoadmapFieldFaithful :
    FieldFaithful VerificationFailureRoadmapUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := verificationFailureRoadmapFields
  field_faithful := verificationFailureRoadmap_fields_faithful

instance verificationFailureRoadmapNontrivial :
    Nontrivial VerificationFailureRoadmapUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨VerificationFailureRoadmapUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      VerificationFailureRoadmapUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate VerificationFailureRoadmapUp :=
  -- BEDC touchpoint anchor: BHist BMark
  verificationFailureRoadmapChapterTasteGate

theorem VerificationFailureRoadmapNameCertObligations
    (R A F D M U B T C P N : BHist) :
    verificationFailureRoadmapFields (VerificationFailureRoadmapUp.mk R A F D M U B T C P N) =
        [R, A, F, D, M, U, B, T, C, P, N] ∧
      Cont R A (append R A) ∧ hsame (append F D) (append F D) ∧
        SemanticNameCert
          (fun h : BHist => hsame h N)
          (fun h : BHist => hsame h N)
          (fun h : BHist => hsame h N)
          (fun h k : BHist => hsame h k) := by
  -- BEDC touchpoint anchor: BHist Cont hsame append SemanticNameCert
  exact
    ⟨rfl, rfl, hsame_refl (append F D),
      {
        core := {
          carrier_inhabited := Exists.intro N (hsame_refl N)
          equiv_refl := by
            intro h _source
            exact hsame_refl h
          equiv_symm := by
            intro _h _k same
            exact hsame_symm same
          equiv_trans := by
            intro _h _k _r sameHK sameKR
            exact hsame_trans sameHK sameKR
          carrier_respects_equiv := by
            intro h k same source
            exact hsame_trans (hsame_symm same) source
        }
        pattern_sound := by
          intro _h source
          exact source
        ledger_sound := by
          intro _h source
          exact source
      }⟩

end BEDC.Derived.VerificationFailureRoadmapUp.TasteGate
