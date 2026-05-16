import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_completion_consumer_refusal
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead finiteRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont source schedule envelopeRead ->
        Cont envelopeRead regular finiteRead ->
          Cont finiteRead sealRow completionRead ->
            PkgSig bundle completionRead pkg ->
              SemanticNameCert
                (fun row : BHist =>
                  BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                    sealRow transport route provenance localCert bundle pkg ∧
                    hsame row completionRead)
                (fun row : BHist =>
                  Cont source schedule envelopeRead ∧ Cont envelopeRead regular finiteRead ∧
                    Cont finiteRead sealRow row ∧ PkgSig bundle completionRead pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle completionRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier sourceScheduleEnvelope envelopeRegularFinite finiteSealCompletion completionPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelope
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed envelopeUnary regularUnary envelopeRegularFinite
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed finiteUnary sealUnary finiteSealCompletion
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead (And.intro
          ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
            sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap,
            trapSealRoute, transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩
          (hsame_refl completionRead))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨sourceScheduleEnvelope, envelopeRegularFinite,
          cont_result_hsame_transport finiteSealCompletion (hsame_symm source.right),
          completionPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport completionUnary (hsame_symm source.right), completionPkg⟩
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
