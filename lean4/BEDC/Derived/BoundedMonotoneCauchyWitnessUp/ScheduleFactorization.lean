import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundedMonotoneCauchyWitnessCarrier_schedule_factorization [AskSetup]
    [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      scheduleRead realSealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont schedule witness scheduleRead →
        Cont scheduleRead sealRow realSealRead →
          PkgSig bundle realSealRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
                    sealRow transport route provenance localCert bundle pkg ∧
                    hsame row realSealRead)
                (fun row : BHist =>
                  UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
                    UnaryHistory row ∧ hsame row realSealRead)
                (fun _row : BHist =>
                  Cont source schedule regular ∧ Cont regular witness trap ∧
                    Cont schedule witness scheduleRead ∧
                      Cont scheduleRead sealRow realSealRead ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle realSealRead pkg)
                hsame ∧
              UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
                UnaryHistory scheduleRead ∧ UnaryHistory realSealRead ∧
                  Cont schedule witness scheduleRead ∧
                    Cont scheduleRead sealRow realSealRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle realSealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier scheduleWitnessRead scheduleReadSealRead realSealPkg
  have carrierPacket :
      BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg :=
    carrier
  obtain ⟨_sourceUnary, _regularUnary, scheduleUnary, witnessUnary, ledgerUnary, _trapUnary,
    sealUnary, _provenanceUnary, sourceScheduleRegular, regularWitnessTrap, _trapSealRoute,
    _transportLocalCertRoute, _routeProvenanceSeal, provenancePkg⟩ := carrier
  have scheduleReadUnary : UnaryHistory scheduleRead :=
    unary_cont_closed scheduleUnary witnessUnary scheduleWitnessRead
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed scheduleReadUnary sealUnary scheduleReadSealRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap
              sealRow transport route provenance localCert bundle pkg ∧ hsame row realSealRead)
          (fun row : BHist =>
            UnaryHistory schedule ∧ UnaryHistory witness ∧ UnaryHistory ledger ∧
              UnaryHistory row ∧ hsame row realSealRead)
          (fun _row : BHist =>
            Cont source schedule regular ∧ Cont regular witness trap ∧
              Cont schedule witness scheduleRead ∧ Cont scheduleRead sealRow realSealRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle realSealRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro realSealRead (And.intro carrierPacket (hsame_refl realSealRead))
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
          intro _row _other same source
          exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
      }
      pattern_sound := by
        intro row source
        have rowUnary : UnaryHistory row :=
          unary_transport realSealUnary (hsame_symm source.right)
        exact
          ⟨scheduleUnary, witnessUnary, ledgerUnary, rowUnary, source.right⟩
      ledger_sound := by
        intro _row _source
        exact
          ⟨sourceScheduleRegular, regularWitnessTrap, scheduleWitnessRead,
            scheduleReadSealRead, provenancePkg, realSealPkg⟩
    }
  exact
    ⟨cert, scheduleUnary, witnessUnary, ledgerUnary, scheduleReadUnary, realSealUnary,
      scheduleWitnessRead, scheduleReadSealRead, provenancePkg, realSealPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
