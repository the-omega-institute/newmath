import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_formal_target_surface [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge' identityTarget
      compositeTarget tripleTarget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg ->
      hsame identityTarget source ->
        Cont target graph compositeTarget ->
          Cont compositeTarget routes tripleTarget ->
            PkgSig bundle tripleTarget pkg ->
              UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory graph ∧
                UnaryHistory landing ∧ UnaryHistory routes ∧ UnaryHistory identityTarget ∧
                  UnaryHistory compositeTarget ∧ UnaryHistory tripleTarget ∧
                    hsame edge edge' ∧ Cont graph edge landing ∧
                      Cont graph edge' landing ∧ Cont landing routes target ∧
                        Cont target graph compositeTarget ∧
                          Cont compositeTarget routes tripleTarget ∧
                            PkgSig bundle tripleTarget pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle PkgSig
  intro classifier identitySame targetGraphComposite compositeRoutesTriple triplePkg
  obtain ⟨carrier, _edgeUnary, _edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', landingRoutesTarget'⟩ := classifier
  obtain ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, _certMatchesEndpoint, _certPkg⟩ := carrier
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport_symm sourceUnary identitySame
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  exact
    ⟨sourceUnary, targetUnary, graphUnary, landingUnary, routesUnary, identityUnary,
      compositeUnary, tripleUnary, edgeSame, graphEdgeLanding, graphEdgeLanding',
      landingRoutesTarget', targetGraphComposite, compositeRoutesTriple, triplePkg⟩

end BEDC.Derived.CertificateCompilerUp
