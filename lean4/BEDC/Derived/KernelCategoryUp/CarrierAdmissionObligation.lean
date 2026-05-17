import BEDC.Derived.KernelCategoryUp

namespace BEDC.Derived.KernelCategoryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

theorem KernelCategoryCarrier_carrier_admission_obligation [AskSetup] [PackageSetup]
    {object hom identity composition associativity unit provenance name admissionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelCategoryCarrier object hom identity composition associativity unit provenance name ->
      hsame admissionRead name ->
        PkgSig bundle admissionRead pkg ->
          UnaryHistory object ∧ CategoryHomCarrier object object identity ∧
            Cont identity composition hom ∧ hsame associativity (append hom composition) ∧
              hsame unit identity ∧ hsame admissionRead name ∧
                PkgSig bundle admissionRead pkg ∧
                  SemanticNameCert
                    (fun row : BHist =>
                      hsame row admissionRead ∧
                        KernelCategoryCarrier object hom identity composition associativity unit
                          provenance name)
                    (fun row : BHist =>
                      hsame row admissionRead ∧ Cont identity composition hom)
                    (fun row : BHist =>
                      hsame row admissionRead ∧ PkgSig bundle admissionRead pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier sameAdmissionName admissionPkg
  have carrierPacket :
      KernelCategoryCarrier object hom identity composition associativity unit provenance name :=
    carrier
  obtain ⟨objectUnary, identityCarrier, compositionRoute, associativitySame, unitSame,
    _nameSame⟩ := carrier
  have sourceAdmission :
      (fun row : BHist =>
        hsame row admissionRead ∧
          KernelCategoryCarrier object hom identity composition associativity unit provenance
            name) admissionRead := by
    exact ⟨hsame_refl admissionRead, carrierPacket⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row admissionRead ∧
            KernelCategoryCarrier object hom identity composition associativity unit provenance
              name)
        (fun row : BHist => hsame row admissionRead ∧ Cont identity composition hom)
        (fun row : BHist => hsame row admissionRead ∧ PkgSig bundle admissionRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro admissionRead sourceAdmission
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, compositionRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, admissionPkg⟩
    }
  exact
    ⟨objectUnary, identityCarrier, compositionRoute, associativitySame, unitSame,
      sameAdmissionName, admissionPkg, cert⟩

end BEDC.Derived.KernelCategoryUp
