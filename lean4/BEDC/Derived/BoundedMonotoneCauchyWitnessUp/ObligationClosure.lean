import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_obligation_closure [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont sealRow BHist.Empty obligationRead ->
        PkgSig bundle obligationRead pkg ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row obligationRead ∧
                  BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger
                    trap sealRow transport route provenance localCert bundle pkg)
              (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
              (fun row : BHist => hsame row obligationRead ∧ PkgSig bundle obligationRead pkg)
              hsame ∧
            UnaryHistory obligationRead ∧
              Cont sealRow BHist.Empty obligationRead ∧ PkgSig bundle obligationRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier sealEmptyObligation obligationPkg
  have carrierFull :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _regularUnary, _scheduleUnary, _witnessUnary, _ledgerUnary,
    _trapUnary, sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap,
    _trapSealRoute, _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ :=
    carrier
  have obligationSameSeal : hsame obligationRead sealRow :=
    cont_deterministic sealEmptyObligation (cont_right_unit sealRow)
  have sealSameObligation : hsame sealRow obligationRead :=
    hsame_symm obligationSameSeal
  have obligationUnary : UnaryHistory obligationRead :=
    unary_transport sealUnary sealSameObligation
  have certCore :
      NameCert
        (fun row : BHist =>
          hsame row obligationRead ∧
            BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
              sealRow transport route provenance localCert bundle pkg)
        hsame := {
    carrier_inhabited :=
      Exists.intro obligationRead (And.intro (hsame_refl obligationRead) carrierFull)
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
      intro _row _other same sourceRow
      exact And.intro (hsame_trans (hsame_symm same) sourceRow.left) sourceRow.right
  }
  have semantic :
      SemanticNameCert
          (fun row : BHist =>
            hsame row obligationRead ∧
              BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                sealRow transport route provenance localCert bundle pkg)
          (fun row : BHist => hsame row sealRow ∧ UnaryHistory row)
          (fun row : BHist => hsame row obligationRead ∧ PkgSig bundle obligationRead pkg)
          hsame := {
    core := certCore
    pattern_sound := by
      intro row sourceRow
      have rowUnary : UnaryHistory row :=
        unary_transport obligationUnary (hsame_symm sourceRow.left)
      exact And.intro (hsame_trans sourceRow.left obligationSameSeal) rowUnary
    ledger_sound := by
      intro row sourceRow
      exact And.intro sourceRow.left obligationPkg
  }
  exact And.intro semantic
    (And.intro obligationUnary (And.intro sealEmptyObligation obligationPkg))

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
