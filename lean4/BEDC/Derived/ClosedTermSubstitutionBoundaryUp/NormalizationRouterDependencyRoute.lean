import BEDC.Derived.ClosedTermSubstitutionBoundaryUp

namespace BEDC.Derived.ClosedTermSubstitutionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryNormalizationRouterDependencyRoute [AskSetup] [PackageSetup]
    {closedProjection router candidate piRow appRow authorized compiler kernel replay provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory closedProjection →
      UnaryHistory router →
        UnaryHistory piRow →
          UnaryHistory authorized →
            UnaryHistory kernel →
              UnaryHistory provenance →
                Cont closedProjection router candidate →
                  Cont candidate piRow appRow →
                    Cont appRow authorized compiler →
                      Cont compiler kernel replay →
                        Cont replay provenance endpoint →
                          PkgSig bundle endpoint pkg →
                            SemanticNameCert
                                (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row router ∨ hsame row candidate ∨ hsame row endpoint)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ PkgSig bundle endpoint pkg)
                                hsame ∧
                              UnaryHistory endpoint := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro closedUnary routerUnary piUnary authorizedUnary kernelUnary provenanceUnary
    closedRouter candidatePi appAuthorized compilerKernel replayProvenance endpointPkg
  have candidateUnary : UnaryHistory candidate :=
    unary_cont_closed closedUnary routerUnary closedRouter
  have appUnary : UnaryHistory appRow :=
    unary_cont_closed candidateUnary piUnary candidatePi
  have compilerUnary : UnaryHistory compiler :=
    unary_cont_closed appUnary authorizedUnary appAuthorized
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed compilerUnary kernelUnary compilerKernel
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed replayUnary provenanceUnary replayProvenance
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row router ∨ hsame row candidate ∨ hsame row endpoint)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint ⟨hsame_refl endpoint, endpointUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, endpointPkg⟩
  }
  exact ⟨cert, endpointUnary⟩

end BEDC.Derived.ClosedTermSubstitutionBoundaryUp
