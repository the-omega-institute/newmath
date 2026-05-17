import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_endpoint_route_determinacy_envelope
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert endpoint endpoint'
      identityTarget compositeTarget tripleTarget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      hsame endpoint target →
        hsame endpoint' target →
          hsame identityTarget source →
            Cont target graph compositeTarget →
              Cont compositeTarget routes tripleTarget →
                PkgSig bundle tripleTarget pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row tripleTarget ∧ UnaryHistory row ∧
                          PkgSig bundle row pkg)
                      (fun row : BHist =>
                        Cont target graph compositeTarget ∧
                          Cont compositeTarget routes row ∧ hsame endpoint endpoint')
                      (fun row : BHist =>
                        PkgSig bundle row pkg ∧ hsame cert (append provenance target))
                      hsame ∧
                    hsame endpoint endpoint' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier endpointSame endpointPrimeSame identitySame targetGraphComposite
    compositeRoutesTriple triplePkg
  obtain ⟨sourceUnary, targetUnary, graphUnary, _landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have endpointDeterminacy : hsame endpoint endpoint' :=
    hsame_trans endpointSame (hsame_symm endpointPrimeSame)
  have _identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed targetUnary graphUnary targetGraphComposite
  have tripleUnary : UnaryHistory tripleTarget :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesTriple
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row tripleTarget ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            Cont target graph compositeTarget ∧
              Cont compositeTarget routes row ∧ hsame endpoint endpoint')
          (fun row : BHist =>
            PkgSig bundle row pkg ∧ hsame cert (append provenance target))
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro tripleTarget ⟨hsame_refl tripleTarget, tripleUnary, triplePkg⟩
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
          exact source
      }
      pattern_sound := by
        intro row source
        cases source.left
        exact ⟨targetGraphComposite, compositeRoutesTriple, endpointDeterminacy⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.right.right, certMatchesEndpoint⟩
    }
  exact ⟨cert, endpointDeterminacy⟩

end BEDC.Derived.CertificateCompilerUp
