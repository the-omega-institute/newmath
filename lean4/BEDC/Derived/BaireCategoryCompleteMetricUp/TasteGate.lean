import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BaireCategoryCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BaireCategoryCompleteMetricUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (B K M D S R Y E H C P N : BHist) : BaireCategoryCompleteMetricUp
  deriving DecidableEq

def BaireCategoryCompleteMetricCarrier [AskSetup] [PackageSetup]
    (B K M D S R Y E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory M ∧ UnaryHistory D ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory Y ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BaireCategoryCompleteMetricNameCert_obligations [AskSetup] [PackageSetup]
    {B K M D S R Y E H C P N denseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCompleteMetricCarrier B K M D S R Y E H C P N bundle pkg →
      Cont C N denseRead →
        PkgSig bundle denseRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row denseRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row B ∨ hsame row K ∨ hsame row M ∨ hsame row D ∨
                  hsame row S ∨ hsame row R ∨ hsame row Y ∨ hsame row E ∨
                    hsame row denseRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont C N denseRead ∧ PkgSig bundle denseRead pkg)
              hsame ∧
            UnaryHistory denseRead := by
  -- BEDC touchpoint anchor: BaireCategoryCompleteMetricCarrier BHist Cont PkgSig hsame SemanticNameCert
  intro carrier replayRoute densePkg
  obtain ⟨_bUnary, _kUnary, _mUnary, _dUnary, _sUnary, _rUnary, _yUnary, _eUnary,
    _hUnary, cUnary, _pUnary, nUnary, _provenancePkg, _namePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed cUnary nUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row denseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row K ∨ hsame row M ∨ hsame row D ∨
              hsame row S ∨ hsame row R ∨ hsame row Y ∨ hsame row E ∨
                hsame row denseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C N denseRead ∧ PkgSig bundle denseRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro denseRead ⟨hsame_refl denseRead, denseUnary⟩
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
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayRoute, densePkg⟩
  }
  exact ⟨cert, denseUnary⟩

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist h

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields :
    BaireCategoryCompleteMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BaireCategoryCompleteMetricUp.mk B K M D S R Y E H C P N =>
      [B, K, M, D, S, R, Y, E, H, C, P, N]

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow :
    BaireCategoryCompleteMetricUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields x).map
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist

private def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt index rest

def BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option BaireCategoryCompleteMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BaireCategoryCompleteMetricUp.mk
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 0 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 1 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 2 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 3 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 4 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 5 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 6 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 7 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 8 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 9 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 10 ef))
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_round_trip
    (x : BaireCategoryCompleteMetricUp) :
    BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
      (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk B K M D S R Y E H C P N =>
      change
        some
          (BaireCategoryCompleteMetricUp.mk
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist B))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist K))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist M))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist D))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist S))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist R))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist Y))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist E))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist H))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist C))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist P))
            (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decodeBHist
              (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (BaireCategoryCompleteMetricUp.mk B K M D S R Y E H C P N)
      rw [BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode B,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode K,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode M,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode D,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode S,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode R,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode Y,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode E,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode H,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode C,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode P,
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_decode_encode N]

private theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_injective
    {x y : BaireCategoryCompleteMetricUp} :
    BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow x =
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
          (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow x) =
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
          (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_round_trip y)))

private theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : BaireCategoryCompleteMetricUp,
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields x =
        BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk B1 K1 M1 D1 S1 R1 Y1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk B2 K2 M2 D2 S2 R2 Y2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance baireCategoryCompleteMetricBHistCarrier :
    BHistCarrier BaireCategoryCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow

instance baireCategoryCompleteMetricChapterTasteGate :
    ChapterTasteGate BaireCategoryCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fromEventFlow
        (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_injective heq)

instance baireCategoryCompleteMetricFieldFaithful :
    FieldFaithful BaireCategoryCompleteMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_fields
  field_faithful := BaireCategoryCompleteMetricTasteGate_single_carrier_alignment_field_faithful

theorem BaireCategoryCompleteMetricTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BaireCategoryCompleteMetricUp) ∧
      Nonempty (FieldFaithful BaireCategoryCompleteMetricUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact ⟨⟨baireCategoryCompleteMetricChapterTasteGate⟩, ⟨baireCategoryCompleteMetricFieldFaithful⟩⟩

end BEDC.Derived.BaireCategoryCompleteMetricUp
