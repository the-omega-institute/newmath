import BEDC.Derived.ModulusOfConvergenceUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.ModulusOfConvergenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

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

theorem ModulusOfConvergenceCarrier_paired_late_window_common_refinement [AskSetup]
    [PackageSetup]
    {precision0 selector0 modulus0 schedule0 witness0 ledger0 provenance0 schedule0'
      witness0' provenance0' precision1 selector1 modulus1 schedule1 witness1 ledger1
      provenance1 schedule1' witness1' provenance1' : BHist}
    {bundle0 bundle1 : ProbeBundle ProbeName} {pkg0 pkg1 : Pkg} :
    ModulusOfConvergenceCarrier precision0 selector0 modulus0 schedule0 witness0 ledger0
        provenance0 bundle0 pkg0 ->
      ModulusOfConvergenceCarrier precision1 selector1 modulus1 schedule1 witness1 ledger1
        provenance1 bundle1 pkg1 ->
        hsame schedule0 schedule0' ->
          hsame witness0 witness0' ->
            hsame provenance0 provenance0' ->
              Cont modulus0 schedule0' witness0' ->
                Cont witness0' ledger0 provenance0' ->
                  PkgSig bundle0 provenance0' pkg0 ->
                    hsame schedule1 schedule1' ->
                      hsame witness1 witness1' ->
                        hsame provenance1 provenance1' ->
                          Cont modulus1 schedule1' witness1' ->
                            Cont witness1' ledger1 provenance1' ->
                              PkgSig bundle1 provenance1' pkg1 ->
                                exists common : BHist,
                                  ModulusOfConvergenceCarrier precision0 selector0 modulus0
                                      schedule0' witness0' ledger0 provenance0' bundle0 pkg0 ∧
                                    ModulusOfConvergenceCarrier precision1 selector1 modulus1
                                      schedule1' witness1' ledger1 provenance1' bundle1 pkg1 ∧
                                      Cont provenance0' precision1 common ∧
                                        UnaryHistory common := by
  -- BEDC touchpoint anchor: ModulusOfConvergenceCarrier BHist Cont PkgSig hsame
  intro leftCarrier rightCarrier sameSchedule0 sameWitness0 sameProvenance0 restrictedWitness0
    restrictedProvenance0 restrictedPkg0 sameSchedule1 sameWitness1 sameProvenance1
    restrictedWitness1 restrictedProvenance1 restrictedPkg1
  obtain ⟨leftRestricted, _leftWitnessSame, _leftProvenanceSame⟩ :=
    ModulusOfConvergenceCarrier_tail_restriction_stability leftCarrier sameSchedule0
      sameWitness0 sameProvenance0 restrictedWitness0 restrictedProvenance0 restrictedPkg0
  obtain ⟨rightRestricted, _rightWitnessSame, _rightProvenanceSame⟩ :=
    ModulusOfConvergenceCarrier_tail_restriction_stability rightCarrier sameSchedule1
      sameWitness1 sameProvenance1 restrictedWitness1 restrictedProvenance1 restrictedPkg1
  obtain ⟨common, commonRoute, commonUnary⟩ :=
    ModulusOfConvergenceCarrier_composition_stability leftRestricted rightRestricted
  exact ⟨common, leftRestricted, rightRestricted, commonRoute, commonUnary⟩

end BEDC.Derived.ModulusOfConvergenceUp
