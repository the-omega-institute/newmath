import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RationalNestedIntervalLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RationalNestedIntervalLimitUp : Type where
  | packet
      (intervals widthLedger endpointWindows regularHandoff realSeal transportRows
        continuationRows provenance nameCert : BHist) :
      RationalNestedIntervalLimitUp
  deriving DecidableEq

def RationalNestedIntervalLimitCarrier : RationalNestedIntervalLimitUp → Prop
  -- BEDC touchpoint anchor: BHist hsame
  | RationalNestedIntervalLimitUp.packet I W E R S H C P N =>
      hsame I I ∧ hsame W W ∧ hsame E E ∧ hsame R R ∧ hsame S S ∧
        hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N

def RationalNestedIntervalLimitNameCertSurface [AskSetup] [PackageSetup]
    (I W E R S H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  hsame I I ∧ hsame W W ∧ hsame E E ∧ hsame R R ∧ hsame S S ∧
    hsame H H ∧ hsame C C ∧ hsame P P ∧ hsame N N ∧
        SemanticNameCert
          (fun row : BHist => hsame row S ∧ hsame row row)
          (fun row : BHist =>
            hsame row S ∧ hsame I I ∧ hsame W W ∧ hsame E E ∧ hsame R R)
          (fun row : BHist => hsame row S ∧ hsame H H ∧ hsame C C ∧
            hsame P P ∧ hsame N N)
          hsame

def rationalNestedIntervalLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rationalNestedIntervalLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rationalNestedIntervalLimitEncodeBHist h

def rationalNestedIntervalLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rationalNestedIntervalLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rationalNestedIntervalLimitDecodeBHist tail)

private theorem rationalNestedIntervalLimit_decode_encode_bhist :
    ∀ h : BHist,
      rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rationalNestedIntervalLimitFields :
    RationalNestedIntervalLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RationalNestedIntervalLimitUp.packet I W E R S H C P N =>
      [I, W, E, R, S, H, C, P, N]

def rationalNestedIntervalLimitToEventFlow :
    RationalNestedIntervalLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (rationalNestedIntervalLimitFields x).map rationalNestedIntervalLimitEncodeBHist

private def rationalNestedIntervalLimitEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      rationalNestedIntervalLimitEventAtDefault index rest

def rationalNestedIntervalLimitFromEventFlow :
    EventFlow → Option RationalNestedIntervalLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RationalNestedIntervalLimitUp.packet
        (rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEventAtDefault 0 ef))
        (rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEventAtDefault 1 ef))
        (rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEventAtDefault 2 ef))
        (rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEventAtDefault 3 ef))
        (rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEventAtDefault 4 ef))
        (rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEventAtDefault 5 ef))
        (rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEventAtDefault 6 ef))
        (rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEventAtDefault 7 ef))
        (rationalNestedIntervalLimitDecodeBHist
          (rationalNestedIntervalLimitEventAtDefault 8 ef)))

private theorem rationalNestedIntervalLimit_round_trip :
    ∀ x : RationalNestedIntervalLimitUp,
      rationalNestedIntervalLimitFromEventFlow
          (rationalNestedIntervalLimitToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | packet I W E R S H C P N =>
      change
        some
          (RationalNestedIntervalLimitUp.packet
            (rationalNestedIntervalLimitDecodeBHist
              (rationalNestedIntervalLimitEncodeBHist I))
            (rationalNestedIntervalLimitDecodeBHist
              (rationalNestedIntervalLimitEncodeBHist W))
            (rationalNestedIntervalLimitDecodeBHist
              (rationalNestedIntervalLimitEncodeBHist E))
            (rationalNestedIntervalLimitDecodeBHist
              (rationalNestedIntervalLimitEncodeBHist R))
            (rationalNestedIntervalLimitDecodeBHist
              (rationalNestedIntervalLimitEncodeBHist S))
            (rationalNestedIntervalLimitDecodeBHist
              (rationalNestedIntervalLimitEncodeBHist H))
            (rationalNestedIntervalLimitDecodeBHist
              (rationalNestedIntervalLimitEncodeBHist C))
            (rationalNestedIntervalLimitDecodeBHist
              (rationalNestedIntervalLimitEncodeBHist P))
            (rationalNestedIntervalLimitDecodeBHist
              (rationalNestedIntervalLimitEncodeBHist N))) =
          some (RationalNestedIntervalLimitUp.packet I W E R S H C P N)
      rw [rationalNestedIntervalLimit_decode_encode_bhist I,
        rationalNestedIntervalLimit_decode_encode_bhist W,
        rationalNestedIntervalLimit_decode_encode_bhist E,
        rationalNestedIntervalLimit_decode_encode_bhist R,
        rationalNestedIntervalLimit_decode_encode_bhist S,
        rationalNestedIntervalLimit_decode_encode_bhist H,
        rationalNestedIntervalLimit_decode_encode_bhist C,
        rationalNestedIntervalLimit_decode_encode_bhist P,
        rationalNestedIntervalLimit_decode_encode_bhist N]

private theorem rationalNestedIntervalLimitToEventFlow_injective
    {x y : RationalNestedIntervalLimitUp} :
    rationalNestedIntervalLimitToEventFlow x =
        rationalNestedIntervalLimitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rationalNestedIntervalLimitFromEventFlow
          (rationalNestedIntervalLimitToEventFlow x) =
        rationalNestedIntervalLimitFromEventFlow
          (rationalNestedIntervalLimitToEventFlow y) :=
    congrArg rationalNestedIntervalLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rationalNestedIntervalLimit_round_trip x).symm
      (Eq.trans hread (rationalNestedIntervalLimit_round_trip y)))

private theorem rationalNestedIntervalLimit_field_faithful :
    ∀ x y : RationalNestedIntervalLimitUp,
      rationalNestedIntervalLimitFields x = rationalNestedIntervalLimitFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | packet I₁ W₁ E₁ R₁ S₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | packet I₂ W₂ E₂ R₂ S₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance rationalNestedIntervalLimitBHistCarrier :
    BHistCarrier RationalNestedIntervalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rationalNestedIntervalLimitToEventFlow
  fromEventFlow := rationalNestedIntervalLimitFromEventFlow

instance rationalNestedIntervalLimitChapterTasteGate :
    ChapterTasteGate RationalNestedIntervalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      rationalNestedIntervalLimitFromEventFlow
          (rationalNestedIntervalLimitToEventFlow x) =
        some x
    exact rationalNestedIntervalLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rationalNestedIntervalLimitToEventFlow_injective heq)

instance rationalNestedIntervalLimitFieldFaithful :
    FieldFaithful RationalNestedIntervalLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := rationalNestedIntervalLimitFields
  field_faithful := rationalNestedIntervalLimit_field_faithful

def taste_gate : ChapterTasteGate RationalNestedIntervalLimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rationalNestedIntervalLimitChapterTasteGate

theorem RationalNestedIntervalLimitCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {I W E R S H C P N : BHist} :
    RationalNestedIntervalLimitCarrier (RationalNestedIntervalLimitUp.packet I W E R S H C P N) ∧
      RationalNestedIntervalLimitNameCertSurface I W E R S H C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have carrier :
      RationalNestedIntervalLimitCarrier
        (RationalNestedIntervalLimitUp.packet I W E R S H C P N) :=
    ⟨hsame_refl I, hsame_refl W, hsame_refl E, hsame_refl R, hsame_refl S,
      hsame_refl H, hsame_refl C, hsame_refl P, hsame_refl N⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row S ∧ hsame row row)
        (fun row : BHist =>
          hsame row S ∧ hsame I I ∧ hsame W W ∧ hsame E E ∧ hsame R R)
        (fun row : BHist => hsame row S ∧ hsame H H ∧ hsame C C ∧ hsame P P ∧
          hsame N N)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro S ⟨hsame_refl S, hsame_refl S⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            hsame_refl _⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, hsame_refl I, hsame_refl W, hsame_refl E, hsame_refl R⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, hsame_refl H, hsame_refl C, hsame_refl P, hsame_refl N⟩
  }
  exact
    ⟨carrier,
      ⟨hsame_refl I, hsame_refl W, hsame_refl E, hsame_refl R, hsame_refl S,
        hsame_refl H, hsame_refl C, hsame_refl P, hsame_refl N, cert⟩⟩

end BEDC.Derived.RationalNestedIntervalLimitUp
