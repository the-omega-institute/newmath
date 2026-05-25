import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ContinuationBigStepUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ContinuationBigStepCarrier [AskSetup] [PackageSetup]
    (source trace terminal read transport replay provenance cert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory trace ∧ UnaryHistory terminal ∧ UnaryHistory read ∧
    UnaryHistory transport ∧ UnaryHistory provenance ∧ UnaryHistory cert ∧
      Cont source trace terminal ∧ Cont terminal read replay ∧ Cont replay cert provenance ∧
        Cont provenance cert transport ∧ PkgSig bundle terminal pkg

def ContinuationBigStepPacket [AskSetup] [PackageSetup]
    (source trace terminal witness transport replay provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory trace ∧ UnaryHistory terminal ∧ UnaryHistory witness ∧
    UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
      UnaryHistory nameCert ∧ Cont source trace replay ∧ Cont replay terminal witness ∧
        Cont witness transport provenance ∧ hsame nameCert nameCert ∧
          PkgSig bundle nameCert pkg

theorem ContinuationBigStepPacket_small_step_factorization [AskSetup] [PackageSetup]
    {source trace terminal witness transport replay provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationBigStepPacket source trace terminal witness transport replay provenance nameCert
        bundle pkg →
      Cont source trace replay ∧ Cont replay terminal witness ∧ UnaryHistory trace ∧
        UnaryHistory terminal ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig UnaryHistory
  intro packet
  cases packet with
  | intro _sourceUnary rest =>
  cases rest with
  | intro traceUnary rest =>
  cases rest with
  | intro terminalUnary rest =>
  cases rest with
  | intro _witnessUnary rest =>
  cases rest with
  | intro _transportUnary rest =>
  cases rest with
  | intro _replayUnary rest =>
  cases rest with
  | intro _provenanceUnary rest =>
  cases rest with
  | intro _nameCertUnary rest =>
  cases rest with
  | intro sourceTraceReplay rest =>
  cases rest with
  | intro replayTerminalWitness rest =>
  cases rest with
  | intro _witnessTransportProvenance rest =>
  cases rest with
  | intro _nameCertSame nameCertPkg =>
      exact
        And.intro sourceTraceReplay
          (And.intro replayTerminalWitness
            (And.intro traceUnary (And.intro terminalUnary nameCertPkg)))

theorem ContinuationBigStepCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source trace terminal read transport replay provenance cert endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationBigStepCarrier source trace terminal read transport replay provenance cert
        bundle pkg ->
      Cont replay cert endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert
              (fun row : BHist =>
                ContinuationBigStepCarrier source trace terminal read transport replay provenance
                  cert bundle pkg ∧ hsame row endpoint)
              (fun row : BHist => hsame row provenance)
              (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
              hsame ∧
            UnaryHistory source ∧ UnaryHistory trace ∧ UnaryHistory terminal ∧
              UnaryHistory endpoint ∧ Cont source trace terminal ∧ Cont terminal read replay ∧
                Cont replay cert endpoint := by
  intro carrier replayCert endpointPkg
  cases carrier with
  | intro sourceUnary rest =>
  cases rest with
  | intro traceUnary rest =>
  cases rest with
  | intro terminalUnary rest =>
  cases rest with
  | intro readUnary rest =>
  cases rest with
  | intro transportUnary rest =>
  cases rest with
  | intro provenanceUnary rest =>
  cases rest with
  | intro certUnary rest =>
  cases rest with
  | intro terminalRow rest =>
  cases rest with
  | intro replayRow rest =>
  cases rest with
  | intro provenanceRow rest =>
  cases rest with
  | intro transportRow terminalPkg =>
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed terminalUnary readUnary replayRow
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary certUnary replayCert
  have sourceAtEndpoint :
      (fun row : BHist =>
        ContinuationBigStepCarrier source trace terminal read transport replay provenance cert
          bundle pkg ∧ hsame row endpoint) endpoint :=
    And.intro
      (And.intro sourceUnary
        (And.intro traceUnary
          (And.intro terminalUnary
            (And.intro readUnary
              (And.intro transportUnary
                (And.intro provenanceUnary
                  (And.intro certUnary
                    (And.intro terminalRow
                      (And.intro replayRow
                        (And.intro provenanceRow
                          (And.intro transportRow terminalPkg)))))))))))
      (hsame_refl endpoint)
  have provenanceSame : hsame endpoint provenance :=
    hsame_symm (cont_deterministic provenanceRow replayCert)
  have certSurface :
      SemanticNameCert
        (fun row : BHist =>
          ContinuationBigStepCarrier source trace terminal read transport replay provenance cert
            bundle pkg ∧ hsame row endpoint)
        (fun row : BHist => hsame row provenance)
        (fun row : BHist => hsame row provenance ∧ PkgSig bundle endpoint pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact And.intro sourceRow.left (hsame_trans (hsame_symm sameRows) sourceRow.right)
    }
    pattern_sound := by
      intro row sourceRow
      exact hsame_trans sourceRow.right provenanceSame
    ledger_sound := by
      intro row sourceRow
      exact And.intro (hsame_trans sourceRow.right provenanceSame) endpointPkg
  }
  exact And.intro certSurface
    (And.intro sourceUnary
      (And.intro traceUnary
        (And.intro terminalUnary
          (And.intro endpointUnary
              (And.intro terminalRow
                (And.intro replayRow replayCert))))))

theorem ContinuationBigStepConsumerExactness [AskSetup] [PackageSetup]
    {source trace terminal witness transport replay provenance nameCert terminalRead namedRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ContinuationBigStepPacket source trace terminal witness transport replay provenance nameCert
        bundle pkg ->
      Cont witness transport terminalRead ->
        Cont terminalRead nameCert namedRead ->
          PkgSig bundle namedRead pkg ->
            Cont source trace replay ∧ Cont replay terminal witness ∧
              Cont witness transport terminalRead ∧ Cont terminalRead nameCert namedRead ∧
                UnaryHistory trace ∧ UnaryHistory terminal ∧ UnaryHistory witness ∧
                  UnaryHistory terminalRead ∧ UnaryHistory namedRead ∧
                    PkgSig bundle nameCert pkg ∧ PkgSig bundle namedRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame PkgSig UnaryHistory ProbeBundle Pkg
  intro packet terminalRoute namedRoute namedPkg
  obtain ⟨sourceTraceReplay, replayTerminalWitness, traceUnary, terminalUnary, nameCertPkg⟩ :=
    ContinuationBigStepPacket_small_step_factorization packet
  obtain ⟨_sourceUnary, _traceUnary, _terminalUnary, witnessUnary, transportUnary,
    _replayUnary, _provenanceUnary, nameCertUnary, _sourceTraceReplay,
    _replayTerminalWitness, _witnessTransportProvenance, _nameCertSame, _nameCertPkg⟩ :=
      packet
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed witnessUnary transportUnary terminalRoute
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed terminalReadUnary nameCertUnary namedRoute
  exact
    ⟨sourceTraceReplay, replayTerminalWitness, terminalRoute, namedRoute, traceUnary,
      terminalUnary, witnessUnary, terminalReadUnary, namedReadUnary, nameCertPkg, namedPkg⟩

end BEDC.Derived.ContinuationBigStepUp
