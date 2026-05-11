import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

/-!
# DyadicPrecisionUp TasteGate carrier.
-/

namespace BEDC.Derived.DyadicPrecisionUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite precision schedule token with the seven BEDC rows visible to consumers. -/
inductive DyadicPrecisionUp : Type where
  | mk :
      (precision radius window transport provenance nameCert ledger : BHist) →
      DyadicPrecisionUp
  deriving DecidableEq

private def encodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: encodeBHist h
  | BHist.e1 h => BMark.b1 :: encodeBHist h

private def decodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (decodeBHist tail)

private theorem decode_encode_bhist : ∀ h : BHist, decodeBHist (encodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def dyadicPrecisionToEventFlow : DyadicPrecisionUp → EventFlow
  | DyadicPrecisionUp.mk precision radius window transport provenance nameCert ledger =>
      [[BMark.b0],
        encodeBHist precision,
        [BMark.b1, BMark.b0],
        encodeBHist radius,
        [BMark.b1, BMark.b1, BMark.b0],
        encodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist nameCert,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        encodeBHist ledger]

private def dyadicPrecisionFromEventFlow : EventFlow → Option DyadicPrecisionUp
  | _tag0 :: precision :: _tag1 :: radius :: _tag2 :: window ::
      _tag3 :: transport :: _tag4 :: provenance :: _tag5 :: nameCert ::
      _tag6 :: ledger :: [] =>
      some (DyadicPrecisionUp.mk (decodeBHist precision) (decodeBHist radius)
        (decodeBHist window) (decodeBHist transport) (decodeBHist provenance)
        (decodeBHist nameCert) (decodeBHist ledger))
  | _ => none

private theorem dyadicPrecision_round_trip :
    ∀ x : DyadicPrecisionUp,
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x := by
  intro x
  cases x with
  | mk precision radius window transport provenance nameCert ledger =>
      simp only [dyadicPrecisionToEventFlow, dyadicPrecisionFromEventFlow, decode_encode_bhist]

private theorem dyadicPrecisionToEventFlow_injective {x y : DyadicPrecisionUp} :
    dyadicPrecisionToEventFlow x = dyadicPrecisionToEventFlow y → x = y := by
  intro heq
  have hread :
      dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) =
        dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow y) :=
    congrArg dyadicPrecisionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicPrecision_round_trip x).symm
      (Eq.trans hread (dyadicPrecision_round_trip y)))

instance dyadicPrecisionBHistCarrier : BHistCarrier DyadicPrecisionUp where
  toEventFlow := dyadicPrecisionToEventFlow
  fromEventFlow := dyadicPrecisionFromEventFlow

instance dyadicPrecisionChapterTasteGate : ChapterTasteGate DyadicPrecisionUp where
  round_trip := by
    intro x
    change dyadicPrecisionFromEventFlow (dyadicPrecisionToEventFlow x) = some x
    exact dyadicPrecision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicPrecisionToEventFlow_injective heq)

/-- Public gate object for the finite dyadic-precision schedule carrier. -/
def taste_gate : ChapterTasteGate DyadicPrecisionUp :=
  dyadicPrecisionChapterTasteGate

def DyadicPrecisionScheduleSurface [AskSetup] [PackageSetup]
    (precision radius window transport provenance nameCert ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist BMark
  UnaryHistory precision ∧ UnaryHistory radius ∧ UnaryHistory window ∧
    UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory nameCert ∧
      UnaryHistory ledger ∧ Cont precision radius transport ∧
        Cont transport window provenance ∧ Cont provenance nameCert ledger ∧
          PkgSig bundle ledger pkg

theorem DyadicPrecisionScheduleSurface_monotone_refinement_handoff [AskSetup] [PackageSetup]
    {precision radius window transport provenance nameCert ledger precision' radius' window'
      transport' provenance' nameCert' ledger' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicPrecisionScheduleSurface precision radius window transport provenance nameCert ledger
        bundle pkg ->
      hsame precision precision' ->
        hsame radius radius' ->
          hsame window window' ->
            hsame nameCert nameCert' ->
              Cont precision' radius' transport' ->
                Cont transport' window' provenance' ->
                  Cont provenance' nameCert' ledger' ->
                    PkgSig bundle ledger' pkg ->
                      DyadicPrecisionScheduleSurface precision' radius' window' transport'
                          provenance' nameCert' ledger' bundle pkg ∧
                        hsame transport transport' ∧ hsame provenance provenance' ∧
                          hsame ledger ledger' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro surface samePrecision sameRadius sameWindow sameNameCert
  intro precisionRadiusTransport' transportWindowProvenance' provenanceNameCertLedger'
    packageLedger'
  obtain ⟨precisionUnary, radiusUnary, windowUnary, _transportUnary, _provenanceUnary,
    nameCertUnary, _ledgerUnary, precisionRadiusTransport, transportWindowProvenance,
    provenanceNameCertLedger, _packageLedger⟩ := surface
  have precisionUnary' : UnaryHistory precision' :=
    unary_transport precisionUnary samePrecision
  have radiusUnary' : UnaryHistory radius' :=
    unary_transport radiusUnary sameRadius
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  have nameCertUnary' : UnaryHistory nameCert' :=
    unary_transport nameCertUnary sameNameCert
  have sameTransport : hsame transport transport' :=
    cont_respects_hsame samePrecision sameRadius precisionRadiusTransport precisionRadiusTransport'
  have transportUnary' : UnaryHistory transport' :=
    unary_cont_closed precisionUnary' radiusUnary' precisionRadiusTransport'
  have sameProvenance : hsame provenance provenance' :=
    cont_respects_hsame sameTransport sameWindow transportWindowProvenance
      transportWindowProvenance'
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_cont_closed transportUnary' windowUnary' transportWindowProvenance'
  have sameLedger : hsame ledger ledger' :=
    cont_respects_hsame sameProvenance sameNameCert provenanceNameCertLedger
      provenanceNameCertLedger'
  have ledgerUnary' : UnaryHistory ledger' :=
    unary_cont_closed provenanceUnary' nameCertUnary' provenanceNameCertLedger'
  exact
    ⟨⟨precisionUnary', radiusUnary', windowUnary', transportUnary', provenanceUnary',
        nameCertUnary', ledgerUnary', precisionRadiusTransport', transportWindowProvenance',
        provenanceNameCertLedger', packageLedger'⟩,
      sameTransport, sameProvenance, sameLedger⟩

theorem DyadicPrecisionUp_tastegate_compiler_obligation_handoff (x : DyadicPrecisionUp) :
    (∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
      (∀ (w : RawEvent) (m : DisplayAlphabet), List.Mem w (BHistCarrier.toEventFlow x) →
        List.Mem m w → m = BMark.b0 ∨ m = BMark.b1) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ChapterTasteGate.no_hidden_input x
  · intro w m hw hm
    exact ChapterTasteGate.conservativity x w m hw hm

end BEDC.Derived.DyadicPrecisionUp
