import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem KernelMorphismCarrier_certificate_compiler_source_lock
    [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert
      compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg →
      Cont source target compilerRead →
        hsame cert compilerRead →
          PkgSig bundle compilerRead pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row compilerRead ∧
                  KernelMorphismCarrier source target graph edgeAdmission classifierLift
                    transport routes provenance cert bundle pkg)
              (fun row : BHist => Cont source target compilerRead ∧ hsame row compilerRead)
              (fun row : BHist => hsame row compilerRead ∧ PkgSig bundle compilerRead pkg)
              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeCompiler _sameCert compilerPkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro compilerRead
          ⟨hsame_refl compilerRead, carrier⟩
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
      exact ⟨routeCompiler, source.left⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, compilerPkg⟩
  }

end BEDC.Derived.KernelMorphismUp
