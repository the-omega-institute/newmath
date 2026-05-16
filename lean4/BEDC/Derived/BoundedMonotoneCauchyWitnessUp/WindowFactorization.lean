import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_window_factorization [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      prefixRead suffixRead locatedRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont source schedule prefixRead →
        Cont prefixRead ledger suffixRead →
          Cont suffixRead trap locatedRead →
            Cont locatedRead sealRow publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                  (fun row : BHist =>
                    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger
                        trap sealRow transport route provenance localCert bundle pkg ∧
                      hsame row publicRead)
                  (fun row : BHist =>
                    Cont source schedule prefixRead ∧
                      Cont prefixRead ledger suffixRead ∧
                        Cont suffixRead trap locatedRead ∧
                          Cont locatedRead sealRow row ∧ PkgSig bundle publicRead pkg)
                  (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sourceSchedulePrefix prefixLedgerSuffix suffixTrapLocated locatedSealPublic
    publicPkg
  have carrierFull :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨sourceUnary, _regularUnary, scheduleUnary, _witnessUnary, ledgerUnary, trapUnary,
    sealUnary, _provenanceUnary, _sourceScheduleRegular, _regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, _provenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed sourceUnary scheduleUnary sourceSchedulePrefix
  have suffixUnary : UnaryHistory suffixRead :=
    unary_cont_closed prefixUnary ledgerUnary prefixLedgerSuffix
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed suffixUnary trapUnary suffixTrapLocated
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed locatedUnary sealUnary locatedSealPublic
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro carrierFull (hsame_refl publicRead))
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
        constructor
        · exact source.left
        · exact hsame_trans (hsame_symm sameRows) source.right
    }
    pattern_sound := by
      intro row source
      constructor
      · exact sourceSchedulePrefix
      · constructor
        · exact prefixLedgerSuffix
        · constructor
          · exact suffixTrapLocated
          · constructor
            · cases source.right
              exact locatedSealPublic
            · exact publicPkg
    ledger_sound := by
      intro row source
      cases source.right
      exact And.intro publicUnary publicPkg
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
