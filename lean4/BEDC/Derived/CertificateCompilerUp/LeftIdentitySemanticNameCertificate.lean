import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerCarrier_left_identity_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert identityTarget
      compositeTarget : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerCarrier source target graph landing routes transport provenance cert
        bundle pkg →
      hsame identityTarget source →
        Cont identityTarget graph compositeTarget →
          PkgSig bundle compositeTarget pkg →
            SemanticNameCert
              (fun row : BHist =>
                hsame row compositeTarget ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
              (fun row : BHist =>
                Cont identityTarget graph row ∧ Cont source graph landing ∧
                  Cont landing routes target)
              (fun row : BHist =>
                PkgSig bundle row pkg ∧ hsame row landing ∧
                  hsame cert (append provenance target))
              (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier identitySame identityGraphComposite compositePkg
  obtain ⟨sourceUnary, _targetUnary, graphUnary, _landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, sourceGraphLanding, landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have compositeSame : hsame compositeTarget landing :=
    cont_respects_hsame identitySame (hsame_refl graph) identityGraphComposite sourceGraphLanding
  have identityUnary : UnaryHistory identityTarget :=
    unary_transport sourceUnary (hsame_symm identitySame)
  have compositeUnary : UnaryHistory compositeTarget :=
    unary_cont_closed identityUnary graphUnary identityGraphComposite
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro compositeTarget
          ⟨hsame_refl compositeTarget, compositeUnary, compositePkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows sourceRow
        cases sameRows
        exact sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      have compositeToRow : hsame compositeTarget row :=
        hsame_symm sourceRow.left
      have identityGraphRow : Cont identityTarget graph row :=
        cont_result_hsame_transport identityGraphComposite compositeToRow
      exact ⟨identityGraphRow, sourceGraphLanding, landingRoutesTarget⟩
    ledger_sound := by
      intro _row sourceRow
      have rowLanding : hsame _ landing :=
        hsame_trans sourceRow.left compositeSame
      exact ⟨sourceRow.right.right, rowLanding, certMatchesEndpoint⟩
  }

end BEDC.Derived.CertificateCompilerUp
