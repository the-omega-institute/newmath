import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_left_identity_public_route_certificate
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert identityTarget
      compositeTarget publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      hsame identityTarget source →
        Cont identityTarget graph compositeTarget →
          Cont compositeTarget routes publicRead →
            PkgSig bundle publicRead pkg →
              SemanticNameCert
                (fun row : BHist =>
                  hsame row publicRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
                (fun row : BHist =>
                  Cont compositeTarget routes row ∧ hsame compositeTarget landing ∧
                    Cont source graph landing ∧ Cont landing routes target)
                (fun row : BHist =>
                  PkgSig bundle row pkg ∧ hsame cert (append provenance target) ∧
                    hsame compositeTarget landing)
                (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier identitySame identityGraphComposite compositeRoutesPublic publicPkg
  obtain ⟨sourceUnary, _targetUnary, graphUnary, _landingUnary, routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have compositeSame : hsame compositeTarget landing :=
    cont_respects_hsame identitySame (hsame_refl graph) identityGraphComposite sourceGraphLanding
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed identityUnary graphUnary identityGraphComposite
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed compositeUnary routesUnary compositeRoutesPublic
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary, publicPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      have publicToRow : hsame publicRead row :=
        hsame_symm sourceRow.left
      have compositeRoutesRow : Cont compositeTarget routes row :=
        cont_result_hsame_transport compositeRoutesPublic publicToRow
      exact ⟨compositeRoutesRow, compositeSame, sourceGraphLanding, landingRoutesTarget⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, certMatchesEndpoint, compositeSame⟩
  }

end BEDC.Derived.CertificateCompilerUp
