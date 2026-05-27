import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FailureCertificateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FailureCertificateUp : Type where
  | mk (N0 C V A B D H K P L : BHist) : FailureCertificateUp
  deriving DecidableEq

def failureCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: failureCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: failureCertificateEncodeBHist h

def failureCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (failureCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (failureCertificateDecodeBHist tail)

private theorem failureCertificateDecode_encode_bhist :
    ∀ h : BHist, failureCertificateDecodeBHist (failureCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def failureCertificateFields : FailureCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FailureCertificateUp.mk N0 C V A B D H K P L => [N0, C, V, A, B, D, H, K, P, L]

def failureCertificateToEventFlow : FailureCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FailureCertificateUp.mk N0 C V A B D H K P L =>
      [[BMark.b0],
        failureCertificateEncodeBHist N0,
        [BMark.b1, BMark.b0],
        failureCertificateEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b0],
        failureCertificateEncodeBHist V,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        failureCertificateEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        failureCertificateEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        failureCertificateEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        failureCertificateEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        failureCertificateEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        failureCertificateEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        failureCertificateEncodeBHist L]

private def failureCertificateRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => failureCertificateRawAt n rest

private def failureCertificateLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => failureCertificateLengthEq n rest

def failureCertificateFromEventFlow : EventFlow → Option FailureCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match failureCertificateLengthEq 20 flow with
      | true =>
          some
            (FailureCertificateUp.mk
              (failureCertificateDecodeBHist (failureCertificateRawAt 1 flow))
              (failureCertificateDecodeBHist (failureCertificateRawAt 3 flow))
              (failureCertificateDecodeBHist (failureCertificateRawAt 5 flow))
              (failureCertificateDecodeBHist (failureCertificateRawAt 7 flow))
              (failureCertificateDecodeBHist (failureCertificateRawAt 9 flow))
              (failureCertificateDecodeBHist (failureCertificateRawAt 11 flow))
              (failureCertificateDecodeBHist (failureCertificateRawAt 13 flow))
              (failureCertificateDecodeBHist (failureCertificateRawAt 15 flow))
              (failureCertificateDecodeBHist (failureCertificateRawAt 17 flow))
              (failureCertificateDecodeBHist (failureCertificateRawAt 19 flow)))
      | false => none

private theorem failureCertificate_round_trip :
    ∀ x : FailureCertificateUp,
      failureCertificateFromEventFlow (failureCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk N0 C V A B D H K P L =>
      change
        some
          (FailureCertificateUp.mk
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist N0))
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist C))
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist V))
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist A))
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist B))
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist D))
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist H))
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist K))
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist P))
            (failureCertificateDecodeBHist (failureCertificateEncodeBHist L))) =
          some (FailureCertificateUp.mk N0 C V A B D H K P L)
      rw [failureCertificateDecode_encode_bhist N0,
        failureCertificateDecode_encode_bhist C,
        failureCertificateDecode_encode_bhist V,
        failureCertificateDecode_encode_bhist A,
        failureCertificateDecode_encode_bhist B,
        failureCertificateDecode_encode_bhist D,
        failureCertificateDecode_encode_bhist H,
        failureCertificateDecode_encode_bhist K,
        failureCertificateDecode_encode_bhist P,
        failureCertificateDecode_encode_bhist L]

private theorem failureCertificateToEventFlow_injective
    {x y : FailureCertificateUp} :
    failureCertificateToEventFlow x = failureCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      failureCertificateFromEventFlow (failureCertificateToEventFlow x) =
        failureCertificateFromEventFlow (failureCertificateToEventFlow y) :=
    congrArg failureCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (failureCertificate_round_trip x).symm
      (Eq.trans hread (failureCertificate_round_trip y)))

private theorem failureCertificate_field_faithful :
    ∀ x y : FailureCertificateUp, failureCertificateFields x = failureCertificateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk N01 C1 V1 A1 B1 D1 H1 K1 P1 L1 =>
      cases y with
      | mk N02 C2 V2 A2 B2 D2 H2 K2 P2 L2 =>
          cases hfields
          rfl

instance failureCertificateBHistCarrier : BHistCarrier FailureCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := failureCertificateToEventFlow
  fromEventFlow := failureCertificateFromEventFlow

instance failureCertificateChapterTasteGate : ChapterTasteGate FailureCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change failureCertificateFromEventFlow (failureCertificateToEventFlow x) = some x
    exact failureCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (failureCertificateToEventFlow_injective heq)

instance failureCertificateFieldFaithful : FieldFaithful FailureCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := failureCertificateFields
  field_faithful := failureCertificate_field_faithful

instance failureCertificateNontrivial : Nontrivial FailureCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FailureCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FailureCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FailureCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  failureCertificateChapterTasteGate

theorem FailureCertificateTasteGate_single_carrier_alignment :
    (∀ h : BHist, failureCertificateDecodeBHist (failureCertificateEncodeBHist h) = h) ∧
      (∀ x : FailureCertificateUp,
        failureCertificateFromEventFlow (failureCertificateToEventFlow x) = some x) ∧
        (∀ x y : FailureCertificateUp,
          failureCertificateToEventFlow x = failureCertificateToEventFlow y → x = y) ∧
          failureCertificateEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨failureCertificateDecode_encode_bhist,
      failureCertificate_round_trip,
      (fun _ _ heq => failureCertificateToEventFlow_injective heq),
      rfl⟩

theorem FailureCertificate_gate_blocking [AskSetup] [PackageSetup]
    {_N0 _C _V A B D H K P L axisGate diagnostic named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont A B axisGate →
      Cont D H diagnostic →
        Cont axisGate K named →
          Cont diagnostic P L →
            PkgSig bundle named pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row axisGate ∧ Cont A B axisGate)
                  (fun row : BHist => Cont A B axisGate ∧ hsame row axisGate)
                  (fun row : BHist =>
                    PkgSig bundle named pkg ∧ Cont axisGate K named ∧ hsame row axisGate)
                  hsame ∧
                Cont A B axisGate ∧ Cont axisGate K named ∧ Cont D H diagnostic ∧
                  Cont diagnostic P L := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro axisRoute diagnosticRoute namedRoute replayRoute pkgNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row axisGate ∧ Cont A B axisGate)
          (fun row : BHist => Cont A B axisGate ∧ hsame row axisGate)
          (fun row : BHist =>
            PkgSig bundle named pkg ∧ Cont axisGate K named ∧ hsame row axisGate)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro axisGate ⟨hsame_refl axisGate, axisRoute⟩
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
          intro _row _other sameRows sourceRow
          exact ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, sourceRow.left⟩
      ledger_sound := by
        intro _row sourceRow
        exact ⟨pkgNamed, namedRoute, sourceRow.left⟩
    }
  exact ⟨cert, axisRoute, namedRoute, diagnosticRoute, replayRoute⟩

theorem FailureCertificate_axis_row_separation
    {N0 C V A B D H K P L A' B' axisGate axisGate' : BHist} :
    Cont A B axisGate →
      Cont A' B' axisGate' →
        A ≠ A' →
          FailureCertificateUp.mk N0 C V A B D H K P L ≠
              FailureCertificateUp.mk N0 C V A' B' D H K P L ∧
            Cont A B axisGate ∧ Cont A' B' axisGate' := by
  -- BEDC touchpoint anchor: BHist Cont
  intro axisRoute axisRoute' axisDistinct
  constructor
  · intro sameCert
    apply axisDistinct
    cases sameCert
    rfl
  · exact ⟨axisRoute, axisRoute'⟩

end BEDC.Derived.FailureCertificateUp
