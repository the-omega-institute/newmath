import BEDC.Derived.BoundedMonotoneCauchyWitnessUp

namespace BEDC.Derived.BoundedMonotoneCauchyWitnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem BoundedMonotoneCauchyWitnessCarrier_real_seal_schedule_exhaustion
    [AskSetup] [PackageSetup]
    {source regular schedule witness ledger trap sealRow transport route provenance localCert
      scheduleRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BoundedMonotoneCauchyWitnessCarrier source regular schedule witness ledger trap sealRow
        transport route provenance localCert bundle pkg ->
      Cont schedule witness scheduleRead ->
        Cont scheduleRead trap sealRead ->
          PkgSig bundle sealRead pkg ->
            hsame (append schedule (append witness trap)) sealRead ∧
              hsame (append schedule witness) scheduleRead ∧
                Cont scheduleRead trap sealRead ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro _carrier scheduleWitness scheduleReadTrap sealReadPkg
  constructor
  · cases scheduleWitness
    cases scheduleReadTrap
    exact (append_assoc schedule witness trap).symm
  · constructor
    · exact scheduleWitness.symm
    · exact ⟨scheduleReadTrap, sealReadPkg⟩

end BEDC.Derived.BoundedMonotoneCauchyWitnessUp
