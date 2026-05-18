import BEDC.Derived.CertificateCompilerUp

namespace BEDC.Derived.CertificateCompilerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CertificateCompilerClassifier_semantic_name_certificate
    [AskSetup] [PackageSetup]
    {source target graph landing routes transport provenance cert edge edge'
      classifierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateCompilerClassifier source target graph landing routes transport provenance cert
        edge edge' bundle pkg →
      Cont edge edge' classifierRead →
        PkgSig bundle classifierRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              hsame row classifierRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
            (fun row : BHist =>
              Cont edge edge' row ∧ Cont graph edge landing ∧
                Cont graph edge' landing ∧ Cont landing routes target)
            (fun row : BHist =>
              PkgSig bundle row pkg ∧ hsame edge edge' ∧
                hsame cert (append provenance target))
            (fun row row' : BHist => hsame row row') := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro classifier edgeClassifierRead classifierPkg
  obtain ⟨carrier, edgeUnary, edgeUnary', edgeSame, graphEdgeLanding,
    graphEdgeLanding', landingRoutesTarget'⟩ := classifier
  obtain ⟨_sourceUnary, _targetUnary, _graphUnary, _landingUnary, _routesUnary,
    _transportUnary, _provenanceUnary, _sourceGraphLanding, _landingRoutesTarget,
    _provenanceTargetCert, certMatchesEndpoint, _certPkg⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed edgeUnary edgeUnary' edgeClassifierRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro classifierRead
          ⟨hsame_refl classifierRead, classifierUnary, classifierPkg⟩
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
      have classifierToRow : hsame classifierRead row :=
        hsame_symm sourceRow.left
      have edgeEdgeRow : Cont edge edge' row :=
        cont_result_hsame_transport edgeClassifierRead classifierToRow
      exact ⟨edgeEdgeRow, graphEdgeLanding, graphEdgeLanding', landingRoutesTarget'⟩
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right.right, edgeSame, certMatchesEndpoint⟩
  }

end BEDC.Derived.CertificateCompilerUp
