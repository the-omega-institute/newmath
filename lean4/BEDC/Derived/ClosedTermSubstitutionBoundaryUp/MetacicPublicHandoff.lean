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

theorem ClosedTermSubstitutionBoundaryMetacicPublicHandoff [AskSetup] [PackageSetup]
    {term value depth sourceClosed valueClosed shiftRow substituteRow ledger audit transport route
      provenance name metacicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ClosedTermSubstitutionBoundaryCarrier term value depth sourceClosed valueClosed shiftRow
        substituteRow ledger audit transport route provenance name bundle pkg ->
      Cont audit route metacicRead ->
        PkgSig bundle metacicRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row metacicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row audit ∨ hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                  hsame row metacicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle metacicRead pkg ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory metacicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier auditRouteRead metacicPkg
  obtain ⟨_termUnary, _valueUnary, _depthUnary, _sourceClosedUnary, _valueClosedUnary,
    _shiftRowUnary, _substituteRowUnary, _ledgerUnary, auditUnary, _transportUnary,
    routeUnary, provenanceUnary, nameUnary, provenancePkg⟩ := carrier
  have metacicUnary : UnaryHistory metacicRead :=
    unary_cont_closed auditUnary routeUnary auditRouteRead
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row metacicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row audit ∨ hsame row route ∨ hsame row provenance ∨ hsame row name ∨
            hsame row metacicRead)
        (fun row : BHist =>
          UnaryHistory row ∧ PkgSig bundle metacicRead pkg ∧ PkgSig bundle provenance pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro metacicRead
        (And.intro (hsame_refl metacicRead) metacicUnary)
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
        intro row row' sameRows source
        have sameRow'Row : hsame row' row := hsame_symm sameRows
        have row'SameMetacic : hsame row' metacicRead :=
          hsame_trans sameRow'Row source.left
        have row'Unary : UnaryHistory row' :=
          unary_transport source.right sameRows
        exact ⟨row'SameMetacic, row'Unary⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro row source
      exact
        ⟨source.right, metacicPkg, provenancePkg⟩
  }
  exact ⟨cert, metacicUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
