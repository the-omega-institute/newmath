import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterRegSeqRatWindow [AskSetup] [PackageSetup]
    (stream directed modulus endpoint regseq transport provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory modulus ∧
    UnaryHistory endpoint ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
      UnaryHistory provenance ∧ Cont stream directed modulus ∧ Cont modulus endpoint regseq ∧
        Cont regseq transport provenance ∧ PkgSig bundle provenance pkg

def CauchyFilterPacket [AskSetup] [PackageSetup]
    (stream directed modulus endpoint regseq transport consumer provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory modulus ∧
    UnaryHistory endpoint ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
      UnaryHistory consumer ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
        Cont stream directed modulus ∧ Cont modulus endpoint regseq ∧
          Cont regseq transport provenance ∧ Cont endpoint regseq transport ∧
            Cont transport consumer provenance ∧ Cont provenance cert consumer ∧
              PkgSig bundle provenance pkg

theorem CauchyFilterPacket_regseqrat_handoff [AskSetup] [PackageSetup]
    {stream directed modulus endpoint regseq transport consumer provenance cert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterPacket stream directed modulus endpoint regseq transport consumer provenance cert
        bundle pkg ->
      CauchyFilterRegSeqRatWindow stream directed modulus endpoint regseq transport provenance
          bundle pkg ∧
        Cont endpoint regseq transport ∧ Cont transport consumer provenance ∧
          PkgSig bundle provenance pkg := by
  intro packet
  obtain ⟨streamUnary, directedUnary, modulusUnary, endpointUnary, regseqUnary,
    transportUnary, _consumerUnary, provenanceUnary, _certUnary, streamDirectedRow,
    modulusEndpointRow, regseqTransportRow, endpointRegseqRow, transportConsumerRow,
    _certConsumerRow, pkgRow⟩ := packet
  exact
    ⟨⟨streamUnary, directedUnary, modulusUnary, endpointUnary, regseqUnary, transportUnary,
        provenanceUnary, streamDirectedRow, modulusEndpointRow, regseqTransportRow, pkgRow⟩,
      endpointRegseqRow, transportConsumerRow, pkgRow⟩

def CauchyFilterCarrier [AskSetup] [PackageSetup]
    (stream directed threshold endpoint regseq transport consumer provenance nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory directed ∧ UnaryHistory threshold ∧
    UnaryHistory endpoint ∧ UnaryHistory regseq ∧ UnaryHistory transport ∧
      UnaryHistory consumer ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont stream directed regseq ∧ Cont regseq threshold transport ∧
          Cont transport endpoint consumer ∧ Cont consumer provenance nameRow ∧
            PkgSig bundle provenance pkg ∧
              SemanticNameCert (fun row : BHist => hsame row nameRow)
                (fun row : BHist => hsame row nameRow)
                (fun row : BHist => hsame row nameRow) hsame

theorem CauchyFilterCarrier_finite_window_coverage [AskSetup] [PackageSetup]
    {stream directed threshold endpoint regseq transport consumer provenance nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterCarrier stream directed threshold endpoint regseq transport consumer provenance
        nameRow bundle pkg ->
      exists observationWindow endpointWindow sealedWindow : BHist,
        Cont stream directed observationWindow ∧
          Cont observationWindow threshold endpointWindow ∧
            Cont endpointWindow endpoint sealedWindow ∧
              UnaryHistory observationWindow ∧
                UnaryHistory endpointWindow ∧ UnaryHistory sealedWindow := by
  intro carrier
  cases carrier with
  | intro streamUnary carrierRest =>
      cases carrierRest with
      | intro directedUnary carrierRest =>
          cases carrierRest with
          | intro thresholdUnary carrierRest =>
              cases carrierRest with
              | intro endpointUnary _carrierRest =>
                  let observationWindow := append stream directed
                  let endpointWindow := append observationWindow threshold
                  let sealedWindow := append endpointWindow endpoint
                  have observationRow : Cont stream directed observationWindow := by
                    rfl
                  have observationUnary : UnaryHistory observationWindow :=
                    unary_repetition_closed_under_continuation streamUnary directedUnary
                      observationRow
                  have endpointRow : Cont observationWindow threshold endpointWindow := by
                    rfl
                  have endpointWindowUnary : UnaryHistory endpointWindow :=
                    unary_repetition_closed_under_continuation observationUnary thresholdUnary
                      endpointRow
                  have sealedRow : Cont endpointWindow endpoint sealedWindow := by
                    rfl
                  have sealedUnary : UnaryHistory sealedWindow :=
                    unary_repetition_closed_under_continuation endpointWindowUnary endpointUnary
                      sealedRow
                  exact ⟨observationWindow, endpointWindow, sealedWindow, observationRow,
                    endpointRow, sealedRow, observationUnary, endpointWindowUnary, sealedUnary⟩

def CauchyFilterFiniteWindowSurface [AskSetup] [PackageSetup]
    (stream window threshold endpoint compatibility transport consumer provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory threshold ∧
    UnaryHistory compatibility ∧ UnaryHistory provenance ∧ Cont stream window transport ∧
      Cont transport threshold endpoint ∧ Cont endpoint compatibility consumer ∧
        PkgSig bundle consumer pkg

theorem CauchyFilterFiniteWindowSurface_real_seal_consumer_boundary [AskSetup] [PackageSetup]
    {stream window threshold endpoint compatibility transport consumer provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterFiniteWindowSurface stream window threshold endpoint compatibility transport
        consumer provenance bundle pkg ->
      UnaryHistory transport ∧ UnaryHistory endpoint ∧ UnaryHistory consumer ∧
        hsame transport (append stream window) ∧ hsame endpoint (append transport threshold) ∧
          hsame consumer (append endpoint compatibility) ∧ PkgSig bundle consumer pkg := by
  intro surface
  have streamUnary : UnaryHistory stream :=
    surface.left
  have windowUnary : UnaryHistory window :=
    surface.right.left
  have thresholdUnary : UnaryHistory threshold :=
    surface.right.right.left
  have compatibilityUnary : UnaryHistory compatibility :=
    surface.right.right.right.left
  have transportRow : Cont stream window transport :=
    surface.right.right.right.right.right.left
  have endpointRow : Cont transport threshold endpoint :=
    surface.right.right.right.right.right.right.left
  have consumerRow : Cont endpoint compatibility consumer :=
    surface.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle consumer pkg :=
    surface.right.right.right.right.right.right.right.right
  have transportUnary : UnaryHistory transport :=
    unary_cont_closed streamUnary windowUnary transportRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed transportUnary thresholdUnary endpointRow
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed endpointUnary compatibilityUnary consumerRow
  exact And.intro transportUnary
    (And.intro endpointUnary
      (And.intro consumerUnary
        (And.intro transportRow
          (And.intro endpointRow
            (And.intro consumerRow pkgSig)))))

end BEDC.Derived.CauchyFilterUp
