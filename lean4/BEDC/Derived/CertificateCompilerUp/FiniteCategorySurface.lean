import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_finite_category_surface [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge'
      identityTarget compositeTarget tripleTarget routeCategory : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg →
      hsame identityTarget source →
        Cont target graph compositeTarget →
          Cont compositeTarget routes tripleTarget →
            Cont tripleTarget cert routeCategory →
              PkgSig bundle routeCategory pkg →
                UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
                  UnaryHistory landing ∧ UnaryHistory routes ∧
                    UnaryHistory provenance ∧ UnaryHistory identityTarget ∧
                      UnaryHistory compositeTarget ∧ UnaryHistory tripleTarget ∧
                        UnaryHistory routeCategory ∧ hsame edge edge' ∧
                          Cont graph edge landing ∧ Cont graph edge' landing ∧
                            Cont target graph compositeTarget ∧
                              Cont compositeTarget routes tripleTarget ∧
                                Cont tripleTarget cert routeCategory ∧
                                  PkgSig bundle cert pkg ∧
                                    PkgSig bundle routeCategory pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro classifier identitySame targetGraphComposite compositeRoutesTriple
    tripleCertRoute routeCategoryPkg
  obtain ⟨carrier, _edgeUnary, _edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', _landingRoutesTarget⟩ := classifier
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, provenanceUnary, _sourceGraphLanding, _landingRoutesTargetCarrier,
    provenanceTargetCert, _certMatchesEndpoint, certPkg⟩ := carrier
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  have routeCategoryUnary : UnaryHistory routeCategory :=
    unary_cont_closed tripleUnary
      (unary_cont_closed provenanceUnary targetUnary provenanceTargetCert)
      tripleCertRoute
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary, provenanceUnary,
      identityUnary, compositeUnary, tripleUnary, routeCategoryUnary, edgeSame,
      graphEdgeLanding, graphEdgeLanding', targetGraphComposite, compositeRoutesTriple,
      tripleCertRoute, certPkg, routeCategoryPkg⟩

end BEDC.Derived.CertificateCompilerUp
