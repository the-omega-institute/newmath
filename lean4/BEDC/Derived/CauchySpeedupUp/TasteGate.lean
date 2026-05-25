import BEDC.Derived.CauchySpeedupUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchySpeedupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

def CauchySpeedupCarrier [AskSetup] [PackageSetup]
    (A J D W R E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont A J W ∧
    Cont W R E ∧
      hsame D D ∧
        Cont H C N ∧
          PkgSig bundle P pkg

theorem CauchySpeedupNameCertObligations [AskSetup] [PackageSetup]
    {A J D W R E H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySpeedupCarrier A J D W R E H C P N bundle pkg ->
      Cont A J W ->
        Cont W R E ->
          PkgSig bundle P pkg ->
            SemanticNameCert
              (fun row : BHist =>
                CauchySpeedupCarrier A J D W R E H C P N bundle pkg ∧ hsame row N)
              (fun row : BHist => Cont A J W ∧ Cont W R E ∧ hsame row N)
              (fun row : BHist => PkgSig bundle P pkg ∧ hsame row N)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier sourceWindow windowSeal provenance
  exact {
    core := {
      carrier_inhabited := Exists.intro N ⟨carrier, hsame_refl N⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨sourceWindow, windowSeal, source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenance, source.right⟩
  }

end BEDC.Derived.CauchySpeedupUp

namespace BEDC.Derived.CauchySpeedupUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate
open BEDC.Derived

def cauchySpeedupEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchySpeedupEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchySpeedupEncodeBHist h

def cauchySpeedupDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchySpeedupDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchySpeedupDecodeBHist tail)

private theorem CauchySpeedupTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchySpeedupFields : CauchySpeedupUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchySpeedupUp.mk A J D W R E H C P N => [A, J, D, W, R, E, H, C, P, N]

def cauchySpeedupToEventFlow : CauchySpeedupUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchySpeedupFields x).map cauchySpeedupEncodeBHist

private def cauchySpeedupEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchySpeedupEventAt index rest

def cauchySpeedupFromEventFlow : EventFlow → Option CauchySpeedupUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CauchySpeedupUp.mk
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 0 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 1 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 2 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 3 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 4 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 5 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 6 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 7 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 8 ef))
          (cauchySpeedupDecodeBHist (cauchySpeedupEventAt 9 ef)))

private theorem CauchySpeedupTasteGate_single_carrier_alignment_round_trip
    (x : CauchySpeedupUp) :
    cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk A J D W R E H C P N =>
      change
        some
          (CauchySpeedupUp.mk
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist A))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist J))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist D))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist W))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist R))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist E))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist H))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist C))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist P))
            (cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist N))) =
          some (CauchySpeedupUp.mk A J D W R E H C P N)
      rw [CauchySpeedupTasteGate_single_carrier_alignment_decode_encode A,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode J,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode D,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode W,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode R,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode E,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode H,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode C,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode P,
        CauchySpeedupTasteGate_single_carrier_alignment_decode_encode N]

private theorem CauchySpeedupTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchySpeedupUp} :
    cauchySpeedupToEventFlow x = cauchySpeedupToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) =
        cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow y) :=
    congrArg cauchySpeedupFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchySpeedupTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchySpeedupTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchySpeedupTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CauchySpeedupUp, cauchySpeedupFields x = cauchySpeedupFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 J1 D1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 J2 D2 W2 R2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchySpeedupBHistCarrier : BHistCarrier CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchySpeedupToEventFlow
  fromEventFlow := cauchySpeedupFromEventFlow

instance cauchySpeedupChapterTasteGate : ChapterTasteGate CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) = some x
    exact CauchySpeedupTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchySpeedupTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance cauchySpeedupFieldFaithful : FieldFaithful CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchySpeedupFields
  field_faithful := CauchySpeedupTasteGate_single_carrier_alignment_fields_faithful

instance cauchySpeedupNontrivial : BEDC.Meta.TasteGate.Nontrivial CauchySpeedupUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchySpeedupUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchySpeedupUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchySpeedupTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchySpeedupUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchySpeedupChapterTasteGate

theorem CauchySpeedupTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CauchySpeedupUp) ∧
      Nonempty (FieldFaithful CauchySpeedupUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial CauchySpeedupUp) ∧
          (∀ h : BHist, cauchySpeedupDecodeBHist (cauchySpeedupEncodeBHist h) = h) ∧
            (∀ x : CauchySpeedupUp,
              cauchySpeedupFromEventFlow (cauchySpeedupToEventFlow x) = some x) ∧
              cauchySpeedupEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨cauchySpeedupChapterTasteGate⟩, ⟨cauchySpeedupFieldFaithful⟩,
      ⟨cauchySpeedupNontrivial⟩,
      CauchySpeedupTasteGate_single_carrier_alignment_decode_encode,
      CauchySpeedupTasteGate_single_carrier_alignment_round_trip, rfl⟩

end BEDC.Derived.CauchySpeedupUp.TasteGate
