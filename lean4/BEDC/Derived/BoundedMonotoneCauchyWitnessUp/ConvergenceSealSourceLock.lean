import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_convergence_seal_source_lock
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      sourceRead finiteRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule sourceRead →
        Cont sourceRead regular finiteRead →
          Cont finiteRead sealRow realRead →
            PkgSig bundle realRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                    sealRow transport route provenance localCert bundle pkg ∧
                    hsame row realRead)
                (fun row : BHist =>
                  Cont source schedule sourceRead ∧ Cont sourceRead regular finiteRead ∧
                    Cont finiteRead sealRow row ∧ PkgSig bundle realRead pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle realRead pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig hsame SemanticNameCert
  intro carrier sourceScheduleRead sourceReadRegularFinite finiteSealReal realPkg
  obtain ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
    sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap, trapSealRoute,
    transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceScheduleRead
  have finiteReadUnary : UnaryHistory finiteRead :=
    unary_cont_closed sourceReadUnary regularUnary sourceReadRegularFinite
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed finiteReadUnary sealUnary finiteSealReal
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realRead (And.intro
          ⟨sourceUnary, regularUnary, scheduleUnary, witnessUnary, ledgerUnary, trapUnary,
            sealUnary, provenanceUnary, sourceScheduleRegular, regularWitnessTrap,
            trapSealRoute, transportLocalCertRoute, routeProvenanceSeal, provenancePkg⟩
          (hsame_refl realRead))
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
        ⟨sourceScheduleRead, sourceReadRegularFinite,
          cont_result_hsame_transport finiteSealReal (hsame_symm source.right), realPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨unary_transport realReadUnary (hsame_symm source.right), realPkg⟩
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
