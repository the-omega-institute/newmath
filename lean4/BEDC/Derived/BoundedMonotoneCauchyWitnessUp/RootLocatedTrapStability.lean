import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem BoundedMonotoneCauchyWitnessCarrier_root_located_trap_stability
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      trapRead sealRead consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg →
      Cont ledger trap trapRead →
        Cont trapRead sealRow sealRead →
          Cont sealRead localCert consumer →
            PkgSig bundle consumer pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row consumer ∧
                    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger
                      trap sealRow transport route provenance localCert bundle pkg)
                (fun row : BHist =>
                  hsame row consumer ∧ Cont ledger trap trapRead ∧
                    Cont trapRead sealRow sealRead ∧ Cont sealRead localCert consumer)
                (fun row : BHist => hsame row consumer ∧ PkgSig bundle consumer pkg)
                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier ledgerTrapRead trapSealRead sealLocalConsumer consumerPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro consumer
          ⟨hsame_refl consumer, carrier⟩
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
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, ledgerTrapRead, trapSealRead, sealLocalConsumer⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerPkg⟩
  }

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
