import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_route_category_boundary [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' identityTarget
      compositeTarget tripleTarget routeCategory : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg →
      hsame identityTarget source →
        Cont target graph compositeTarget →
          Cont compositeTarget routes tripleTarget →
            Cont tripleTarget cert routeCategory →
              PkgSig bundle routeCategory pkg →
                SemanticNameCert
                  (fun row : BHist => hsame row routeCategory ∧ UnaryHistory row)
                  (fun row : BHist =>
                    Cont target graph compositeTarget ∧
                      Cont compositeTarget routes tripleTarget ∧
                        Cont tripleTarget cert routeCategory ∧ hsame row routeCategory)
                  (fun row : BHist => hsame row routeCategory ∧ PkgSig bundle routeCategory pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory Cont ProbeBundle Pkg SemanticNameCert
  intro classifier _identitySame targetGraphComposite compositeRoutesTriple
    tripleCertRouteCategory routeCategoryPkg
  obtain ⟨carrier, _edgeUnary, _edgeUnary', _edgeSame, _graphEdgeLanding,
    _graphEdgeLanding', _landingRoutesTarget'⟩ := classifier
  obtain ⟨_sourceUnary, targetUnary, graphUnary, _landingUnary, routesUnary,
    _transportUnary, provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    provenanceTargetCert, _certMatchesEndpoint, _certPkg⟩ := carrier
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  have certUnary : UnaryHistory cert :=
    unary_cont_closed provenanceUnary targetUnary provenanceTargetCert
  have routeCategoryUnary : UnaryHistory routeCategory :=
    unary_cont_closed tripleUnary certUnary tripleCertRouteCategory
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro routeCategory ⟨hsame_refl routeCategory, routeCategoryUnary⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro row sourceRow
      exact ⟨targetGraphComposite, compositeRoutesTriple, tripleCertRouteCategory, sourceRow.left⟩
    ledger_sound := by
      intro row sourceRow
      exact ⟨sourceRow.left, routeCategoryPkg⟩
  }

end BEDC.Derived.CertificateCompilerUp
