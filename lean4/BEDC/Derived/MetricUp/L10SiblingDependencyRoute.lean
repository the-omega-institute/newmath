import BEDC.Derived.MetricUp.L10SiblingLatticeRoute

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricL10SiblingDependencyRoute_surface [AskSetup] [PackageSetup]
    {located sone real stream regseq dyadic locatedRoute soneRoute realRoute l10 provenance
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory located →
      UnaryHistory sone →
        UnaryHistory real →
          UnaryHistory stream →
            UnaryHistory regseq →
              UnaryHistory dyadic →
                UnaryHistory provenance →
                  Cont located sone locatedRoute →
                    Cont stream regseq soneRoute →
                      Cont dyadic real realRoute →
                        Cont locatedRoute soneRoute l10 →
                          Cont l10 provenance endpoint →
                            PkgSig bundle endpoint pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row l10 ∨ hsame row provenance ∨
                                      hsame row endpoint)
                                  (fun row : BHist =>
                                    hsame row endpoint ∧ PkgSig bundle endpoint pkg)
                                  hsame ∧
                                MetricDistanceWitness locatedRoute soneRoute l10 ∧
                                  UnaryHistory endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro locatedUnary soneUnary realUnary streamUnary regseqUnary dyadicUnary
    provenanceUnary locatedSoneRoute streamRegseqRoute dyadicRealRoute
    locatedRouteSoneRoute l10ProvenanceEndpoint endpointPkg
  have locatedRouteUnary : UnaryHistory locatedRoute :=
    unary_cont_closed locatedUnary soneUnary locatedSoneRoute
  have soneRouteUnary : UnaryHistory soneRoute :=
    unary_cont_closed streamUnary regseqUnary streamRegseqRoute
  have _realRouteUnary : UnaryHistory realRoute :=
    unary_cont_closed dyadicUnary realUnary dyadicRealRoute
  have l10Unary : UnaryHistory l10 :=
    unary_cont_closed locatedRouteUnary soneRouteUnary locatedRouteSoneRoute
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed l10Unary provenanceUnary l10ProvenanceEndpoint
  have distanceWitness : MetricDistanceWitness locatedRoute soneRoute l10 :=
    ⟨locatedRouteUnary, soneRouteUnary, l10Unary, locatedRouteSoneRoute⟩
  have sourceEndpoint :
      (fun row : BHist => hsame row endpoint ∧ UnaryHistory row) endpoint := by
    exact ⟨hsame_refl endpoint, endpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row endpoint ∧ UnaryHistory row)
          (fun row : BHist => hsame row l10 ∨ hsame row provenance ∨ hsame row endpoint)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle endpoint pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceEndpoint
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
      exact ⟨source.left, endpointPkg⟩
  }
  exact ⟨cert, distanceWitness, endpointUnary, endpointPkg⟩

end BEDC.Derived.MetricUp
