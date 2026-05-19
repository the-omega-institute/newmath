import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FormalConstantEmpiricalValueBoundaryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FormalConstantEmpiricalValueBoundaryUp : Type where
  | mk (formal empirical calibration uncertainty reproducibility failure transport replay
      provenance localCert : BHist) : FormalConstantEmpiricalValueBoundaryUp
  deriving DecidableEq

def formalConstantEmpiricalValueBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: formalConstantEmpiricalValueBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: formalConstantEmpiricalValueBoundaryEncodeBHist h

def formalConstantEmpiricalValueBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (formalConstantEmpiricalValueBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (formalConstantEmpiricalValueBoundaryDecodeBHist tail)

private theorem formalConstantEmpiricalValueBoundary_decode_encode_bhist :
    ∀ h : BHist,
      formalConstantEmpiricalValueBoundaryDecodeBHist
        (formalConstantEmpiricalValueBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def formalConstantEmpiricalValueBoundaryFields :
    FormalConstantEmpiricalValueBoundaryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FormalConstantEmpiricalValueBoundaryUp.mk formal empirical calibration uncertainty
      reproducibility failure transport replay provenance localCert =>
      [formal, empirical, calibration, uncertainty, reproducibility, failure, transport, replay,
        provenance, localCert]

def formalConstantEmpiricalValueBoundaryToEventFlow :
    FormalConstantEmpiricalValueBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FormalConstantEmpiricalValueBoundaryUp.mk formal empirical calibration uncertainty
      reproducibility failure transport replay provenance localCert =>
      [formalConstantEmpiricalValueBoundaryEncodeBHist formal,
        formalConstantEmpiricalValueBoundaryEncodeBHist empirical,
        formalConstantEmpiricalValueBoundaryEncodeBHist calibration,
        formalConstantEmpiricalValueBoundaryEncodeBHist uncertainty,
        formalConstantEmpiricalValueBoundaryEncodeBHist reproducibility,
        formalConstantEmpiricalValueBoundaryEncodeBHist failure,
        formalConstantEmpiricalValueBoundaryEncodeBHist transport,
        formalConstantEmpiricalValueBoundaryEncodeBHist replay,
        formalConstantEmpiricalValueBoundaryEncodeBHist provenance,
        formalConstantEmpiricalValueBoundaryEncodeBHist localCert]

private def formalConstantEmpiricalValueBoundaryRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => formalConstantEmpiricalValueBoundaryRawAt n rest

private def formalConstantEmpiricalValueBoundaryLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => formalConstantEmpiricalValueBoundaryLengthEq n rest

def formalConstantEmpiricalValueBoundaryFromEventFlow :
    EventFlow → Option FormalConstantEmpiricalValueBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match formalConstantEmpiricalValueBoundaryLengthEq 10 flow with
      | true =>
          some
            (FormalConstantEmpiricalValueBoundaryUp.mk
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 0 flow))
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 1 flow))
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 2 flow))
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 3 flow))
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 4 flow))
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 5 flow))
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 6 flow))
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 7 flow))
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 8 flow))
              (formalConstantEmpiricalValueBoundaryDecodeBHist
                (formalConstantEmpiricalValueBoundaryRawAt 9 flow)))
      | false => none

private theorem formalConstantEmpiricalValueBoundary_round_trip :
    ∀ x : FormalConstantEmpiricalValueBoundaryUp,
      formalConstantEmpiricalValueBoundaryFromEventFlow
          (formalConstantEmpiricalValueBoundaryToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk formal empirical calibration uncertainty reproducibility failure transport replay
      provenance localCert =>
      change
        some
          (FormalConstantEmpiricalValueBoundaryUp.mk
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist formal))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist empirical))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist calibration))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist uncertainty))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist reproducibility))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist failure))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist transport))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist replay))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist provenance))
            (formalConstantEmpiricalValueBoundaryDecodeBHist
              (formalConstantEmpiricalValueBoundaryEncodeBHist localCert))) =
          some
            (FormalConstantEmpiricalValueBoundaryUp.mk formal empirical calibration uncertainty
              reproducibility failure transport replay provenance localCert)
      exact congrArg some
        (by
          rw [formalConstantEmpiricalValueBoundary_decode_encode_bhist formal,
            formalConstantEmpiricalValueBoundary_decode_encode_bhist empirical,
            formalConstantEmpiricalValueBoundary_decode_encode_bhist calibration,
            formalConstantEmpiricalValueBoundary_decode_encode_bhist uncertainty,
            formalConstantEmpiricalValueBoundary_decode_encode_bhist reproducibility,
            formalConstantEmpiricalValueBoundary_decode_encode_bhist failure,
            formalConstantEmpiricalValueBoundary_decode_encode_bhist transport,
            formalConstantEmpiricalValueBoundary_decode_encode_bhist replay,
            formalConstantEmpiricalValueBoundary_decode_encode_bhist provenance,
            formalConstantEmpiricalValueBoundary_decode_encode_bhist localCert])

private theorem formalConstantEmpiricalValueBoundaryToEventFlow_injective
    {x y : FormalConstantEmpiricalValueBoundaryUp} :
    formalConstantEmpiricalValueBoundaryToEventFlow x =
      formalConstantEmpiricalValueBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      formalConstantEmpiricalValueBoundaryFromEventFlow
          (formalConstantEmpiricalValueBoundaryToEventFlow x) =
        formalConstantEmpiricalValueBoundaryFromEventFlow
          (formalConstantEmpiricalValueBoundaryToEventFlow y) :=
    congrArg formalConstantEmpiricalValueBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (formalConstantEmpiricalValueBoundary_round_trip x).symm
      (Eq.trans hread (formalConstantEmpiricalValueBoundary_round_trip y)))

private theorem formalConstantEmpiricalValueBoundary_fields :
    ∀ x y : FormalConstantEmpiricalValueBoundaryUp,
      formalConstantEmpiricalValueBoundaryFields x =
        formalConstantEmpiricalValueBoundaryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk formal₁ empirical₁ calibration₁ uncertainty₁ reproducibility₁ failure₁ transport₁
      replay₁ provenance₁ localCert₁ =>
      cases y with
      | mk formal₂ empirical₂ calibration₂ uncertainty₂ reproducibility₂ failure₂ transport₂
          replay₂ provenance₂ localCert₂ =>
          cases hfields
          rfl

instance formalConstantEmpiricalValueBoundaryBHistCarrier :
    BHistCarrier FormalConstantEmpiricalValueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := formalConstantEmpiricalValueBoundaryToEventFlow
  fromEventFlow := formalConstantEmpiricalValueBoundaryFromEventFlow

instance formalConstantEmpiricalValueBoundaryChapterTasteGate :
    ChapterTasteGate FormalConstantEmpiricalValueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    exact formalConstantEmpiricalValueBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (formalConstantEmpiricalValueBoundaryToEventFlow_injective heq)

instance formalConstantEmpiricalValueBoundaryFieldFaithful :
    FieldFaithful FormalConstantEmpiricalValueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := formalConstantEmpiricalValueBoundaryFields
  field_faithful := formalConstantEmpiricalValueBoundary_fields

instance formalConstantEmpiricalValueBoundaryNontrivial :
    Nontrivial FormalConstantEmpiricalValueBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FormalConstantEmpiricalValueBoundaryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FormalConstantEmpiricalValueBoundaryUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FormalConstantEmpiricalValueBoundaryUp :=
  -- BEDC touchpoint anchor: BHist BMark
  formalConstantEmpiricalValueBoundaryChapterTasteGate

theorem FormalConstantEmpiricalValueBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      formalConstantEmpiricalValueBoundaryDecodeBHist
        (formalConstantEmpiricalValueBoundaryEncodeBHist h) = h) ∧
      (∀ x : FormalConstantEmpiricalValueBoundaryUp,
        formalConstantEmpiricalValueBoundaryFromEventFlow
          (formalConstantEmpiricalValueBoundaryToEventFlow x) = some x) ∧
        (∀ x y : FormalConstantEmpiricalValueBoundaryUp,
          formalConstantEmpiricalValueBoundaryToEventFlow x =
            formalConstantEmpiricalValueBoundaryToEventFlow y → x = y) ∧
          formalConstantEmpiricalValueBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨formalConstantEmpiricalValueBoundary_decode_encode_bhist,
      formalConstantEmpiricalValueBoundary_round_trip,
      (fun _ _ heq => formalConstantEmpiricalValueBoundaryToEventFlow_injective heq),
      rfl⟩

theorem FormalConstantEmpiricalValueBoundaryNoncollapse
    {formal empirical calibration uncertainty reproducibility failure transport replay provenance
      localCert comparison : BHist} :
    formalConstantEmpiricalValueBoundaryFields
        (FormalConstantEmpiricalValueBoundaryUp.mk formal empirical calibration uncertainty
          reproducibility failure transport replay provenance localCert) =
      [formal, empirical, calibration, uncertainty, reproducibility, failure, transport, replay,
        provenance, localCert] →
      Cont formal empirical comparison →
        UnaryHistory formal →
          UnaryHistory empirical →
            UnaryHistory comparison ∧ Cont formal empirical comparison ∧ hsame failure failure := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro hfields formalEmpiricalComparison formalUnary empiricalUnary
  cases hfields
  have comparisonUnary : UnaryHistory comparison :=
    unary_cont_closed formalUnary empiricalUnary formalEmpiricalComparison
  exact ⟨comparisonUnary, formalEmpiricalComparison, hsame_refl failure⟩

theorem FormalConstantEmpiricalValueBoundaryNameCertObligations
    {formal empirical calibration uncertainty reproducibility failure transport replay provenance
      localCert measurementReplay calibrationReplay : BHist} :
    formalConstantEmpiricalValueBoundaryFields
        (FormalConstantEmpiricalValueBoundaryUp.mk formal empirical calibration uncertainty
          reproducibility failure transport replay provenance localCert) =
      [formal, empirical, calibration, uncertainty, reproducibility, failure, transport, replay,
        provenance, localCert] →
      Cont empirical calibration measurementReplay →
        Cont uncertainty reproducibility calibrationReplay →
          UnaryHistory empirical →
            UnaryHistory calibration →
              UnaryHistory uncertainty →
                UnaryHistory reproducibility →
                  UnaryHistory measurementReplay ∧
                    UnaryHistory calibrationReplay ∧
                      Cont empirical calibration measurementReplay ∧
                        Cont uncertainty reproducibility calibrationReplay ∧ hsame failure failure := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro hfields measurementRoute calibrationRoute empiricalUnary calibrationUnary
    uncertaintyUnary reproducibilityUnary
  cases hfields
  have measurementReplayUnary : UnaryHistory measurementReplay :=
    unary_cont_closed empiricalUnary calibrationUnary measurementRoute
  have calibrationReplayUnary : UnaryHistory calibrationReplay :=
    unary_cont_closed uncertaintyUnary reproducibilityUnary calibrationRoute
  exact
    ⟨measurementReplayUnary, calibrationReplayUnary, measurementRoute, calibrationRoute,
      hsame_refl failure⟩

end BEDC.Derived.FormalConstantEmpiricalValueBoundaryUp
