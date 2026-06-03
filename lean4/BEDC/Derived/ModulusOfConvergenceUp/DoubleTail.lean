import BEDC.Derived.ModulusOfConvergenceUp

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem ModulusOfConvergenceCarrier_synchronized_double_tail_restriction [AskSetup]
    [PackageSetup]
    {precision selector modulus schedule witness ledger provenance schedule1 witness1 provenance1
      schedule2 witness2 provenance2 : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModulusOfConvergenceCarrier precision selector modulus schedule witness ledger provenance
        bundle pkg ->
      hsame schedule schedule1 ->
        hsame witness witness1 ->
          hsame provenance provenance1 ->
            Cont modulus schedule1 witness1 ->
              Cont witness1 ledger provenance1 ->
                PkgSig bundle provenance1 pkg ->
                  hsame schedule1 schedule2 ->
                    hsame witness1 witness2 ->
                      hsame provenance1 provenance2 ->
                        Cont modulus schedule2 witness2 ->
                          Cont witness2 ledger provenance2 ->
                            PkgSig bundle provenance2 pkg ->
                              ModulusOfConvergenceCarrier precision selector modulus schedule2
                                  witness2 ledger provenance2 bundle pkg ∧
                                hsame witness witness2 ∧ hsame provenance provenance2 := by
  intro carrier sameSchedule sameWitness sameProvenance firstWitness firstProvenance firstPkg
  intro sameScheduleNext sameWitnessNext sameProvenanceNext secondWitness secondProvenance
    secondPkg
  obtain ⟨firstCarrier, sameWitnessFirst, sameProvenanceFirst⟩ :=
    ModulusOfConvergenceCarrier_tail_restriction_stability carrier sameSchedule sameWitness
      sameProvenance firstWitness firstProvenance firstPkg
  obtain ⟨secondCarrier, sameWitnessSecond, sameProvenanceSecond⟩ :=
    ModulusOfConvergenceCarrier_tail_restriction_stability firstCarrier sameScheduleNext
      sameWitnessNext sameProvenanceNext secondWitness secondProvenance secondPkg
  exact
    ⟨secondCarrier, hsame_trans sameWitnessFirst sameWitnessSecond,
      hsame_trans sameProvenanceFirst sameProvenanceSecond⟩

end BEDC.Derived.ModulusOfConvergenceUp
