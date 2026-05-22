import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberRootRadiusWindowConsumerExactness [AskSetup]
    [PackageSetup]
    {cover window radius mesh transport route provenance nameRow rootSurface compactConsumer
      continuousConsumer uniformConsumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg →
      Cont route nameRow rootSurface →
        Cont rootSurface radius compactConsumer →
          Cont compactConsumer mesh continuousConsumer →
            Cont continuousConsumer route uniformConsumer →
              PkgSig bundle uniformConsumer pkg →
                UnaryHistory rootSurface ∧ UnaryHistory compactConsumer ∧
                  UnaryHistory continuousConsumer ∧ UnaryHistory uniformConsumer ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row uniformConsumer ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row cover ∨ hsame row window ∨ hsame row radius ∨
                          hsame row mesh ∨ hsame row rootSurface ∨
                            hsame row compactConsumer ∨ hsame row continuousConsumer ∨
                              hsame row uniformConsumer)
                      (fun row : BHist =>
                        PkgSig bundle uniformConsumer pkg ∧ hsame row uniformConsumer)
                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier routeNameRoot rootRadiusCompact compactMeshContinuous
    continuousRouteUniform uniformPkg
  obtain ⟨_coverUnary, _windowUnary, radiusUnary, meshUnary, _transportUnary, routeUnary,
    _provenanceUnary, nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, _provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootSurface :=
    unary_cont_closed routeUnary nameRowUnary routeNameRoot
  have compactUnary : UnaryHistory compactConsumer :=
    unary_cont_closed rootUnary radiusUnary rootRadiusCompact
  have continuousUnary : UnaryHistory continuousConsumer :=
    unary_cont_closed compactUnary meshUnary compactMeshContinuous
  have uniformUnary : UnaryHistory uniformConsumer :=
    unary_cont_closed continuousUnary routeUnary continuousRouteUniform
  have sourceUniform :
      (fun row : BHist => hsame row uniformConsumer ∧ UnaryHistory row) uniformConsumer := by
    exact ⟨hsame_refl uniformConsumer, uniformUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row uniformConsumer ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row cover ∨ hsame row window ∨ hsame row radius ∨
            hsame row mesh ∨ hsame row rootSurface ∨ hsame row compactConsumer ∨
              hsame row continuousConsumer ∨ hsame row uniformConsumer)
        (fun row : BHist => PkgSig bundle uniformConsumer pkg ∧ hsame row uniformConsumer)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro uniformConsumer sourceUniform
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
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨uniformPkg, source.left⟩
    }
  exact ⟨rootUnary, compactUnary, continuousUnary, uniformUnary, cert⟩

end BEDC.Derived.FiniteLebesgueNumberUp
