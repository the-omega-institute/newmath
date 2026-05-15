import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_real_observation_seal_factorization
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      envelopeRead finiteRead observationRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule envelopeRead →
        Cont envelopeRead regular finiteRead →
          Cont finiteRead trap observationRead →
            Cont observationRead sealRow sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger
                        trap sealRow transport route provenance localCert bundle pkg ∧
                      hsame row sealRead)
                  (fun row : BHist =>
                    Cont source schedule envelopeRead ∧
                      Cont envelopeRead regular finiteRead ∧
                        Cont finiteRead trap observationRead ∧
                          Cont observationRead sealRow row ∧ PkgSig bundle sealRead pkg)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle sealRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont Pkg ProbeBundle SemanticNameCert UnaryHistory hsame
  intro carrier sourceScheduleEnvelope envelopeRegularFinite finiteTrapObservation
    observationSeal sealPkg
  have carrierFull :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, _witnessUnary, _ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have envelopeUnary : UnaryHistory envelopeRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleEnvelope
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed envelopeUnary regularUnary envelopeRegularFinite
  have observationUnary : UnaryHistory observationRead :=
    unary_cont_closed finiteUnary trapUnary finiteTrapObservation
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed observationUnary sealUnary observationSeal
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead (And.intro carrierFull (hsame_refl sealRead))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro row source
      cases source.right
      exact
        And.intro sourceScheduleEnvelope
          (And.intro envelopeRegularFinite
            (And.intro finiteTrapObservation (And.intro observationSeal sealPkg)))
    ledger_sound := by
      intro row source
      cases source.right
      exact And.intro sealReadUnary sealPkg
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
