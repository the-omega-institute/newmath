import BEDC.Derived.KernelMorphismUp

namespace BEDC.Derived.KernelMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem KernelMorphismCarrier_certificate_compiler_handoff [AskSetup] [PackageSetup]
    {source target graph edgeAdmission classifierLift transport routes provenance cert
      compilerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KernelMorphismCarrier source target graph edgeAdmission classifierLift transport routes
        provenance cert bundle pkg →
      Cont cert target compilerRead →
        PkgSig bundle compilerRead pkg →
          SemanticNameCert
            (fun row : BHist => hsame row compilerRead ∧ UnaryHistory row ∧
              PkgSig bundle row pkg)
            (fun row : BHist => Cont cert target row ∧ Cont source graph edgeAdmission ∧
              Cont edgeAdmission classifierLift target)
            (fun row : BHist => PkgSig bundle row pkg ∧ PkgSig bundle cert pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont PkgSig
  intro carrier certTargetCompiler compilerPkg
  obtain ⟨sourceUnary, targetUnary, _graphUnary, _edgeUnary, _liftUnary, _transportUnary,
    _routesUnary, _provenanceUnary, certUnary, sourceGraphEdge, edgeLiftTarget,
    _transportRoutesProvenance, _provenancePkg, certPkg⟩ := carrier
  have compilerUnary : UnaryHistory compilerRead :=
    unary_cont_closed certUnary targetUnary certTargetCompiler
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro compilerRead ⟨hsame_refl compilerRead, compilerUnary, compilerPkg⟩
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
        cases same
        exact
          ⟨source.left, source.right.left, source.right.right⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨cont_result_hsame_transport certTargetCompiler (hsame_symm source.left),
          sourceGraphEdge, edgeLiftTarget⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right.right, certPkg⟩
  }

end BEDC.Derived.KernelMorphismUp
