import BEDC.Derived.ClosedTermSubstitutionBoundaryUp.AuthorizedRecursorAuditRoute
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryMetacicDependency [AskSetup] [PackageSetup]
    {term value depth sourceClosed valueClosed shiftRow substituteRow ledger audit transport route
      provenance name metacicRead normalizationRead confluenceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryCarrier term value depth sourceClosed valueClosed shiftRow
        substituteRow ledger audit transport route provenance name bundle pkg ->
      Cont audit route metacicRead ->
        Cont metacicRead route normalizationRead ->
          Cont metacicRead audit confluenceRead ->
            PkgSig bundle metacicRead pkg ->
              PkgSig bundle normalizationRead pkg ->
                PkgSig bundle confluenceRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row confluenceRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row sourceClosed ∨ hsame row valueClosed ∨
                          hsame row substituteRow ∨ hsame row audit ∨ hsame row route ∨
                            hsame row metacicRead ∨ hsame row confluenceRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont audit route metacicRead ∧
                          Cont metacicRead audit confluenceRead ∧ PkgSig bundle confluenceRead pkg)
                      hsame ∧
                    UnaryHistory metacicRead ∧ UnaryHistory normalizationRead ∧
                      UnaryHistory confluenceRead ∧ PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier auditRouteMetacic metacicRouteNormalization metacicAuditConfluence _metacicPkg
    _normalizationPkg confluencePkg
  obtain ⟨_termUnary, _valueUnary, _depthUnary, _sourceClosedUnary, _valueClosedUnary,
    _shiftRowUnary, _substituteRowUnary, _ledgerUnary, auditUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameUnary, provenancePkg⟩ := carrier
  have metacicUnary : UnaryHistory metacicRead :=
    unary_cont_closed auditUnary routeUnary auditRouteMetacic
  have normalizationUnary : UnaryHistory normalizationRead :=
    unary_cont_closed metacicUnary routeUnary metacicRouteNormalization
  have confluenceUnary : UnaryHistory confluenceRead :=
    unary_cont_closed metacicUnary auditUnary metacicAuditConfluence
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row confluenceRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceClosed ∨ hsame row valueClosed ∨ hsame row substituteRow ∨
              hsame row audit ∨ hsame row route ∨ hsame row metacicRead ∨
                hsame row confluenceRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont audit route metacicRead ∧
              Cont metacicRead audit confluenceRead ∧ PkgSig bundle confluenceRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro confluenceRead
        ⟨hsame_refl confluenceRead, confluenceUnary⟩
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
        intro row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, auditRouteMetacic, metacicAuditConfluence, confluencePkg⟩
  }
  exact ⟨cert, metacicUnary, normalizationUnary, confluenceUnary, provenancePkg⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
