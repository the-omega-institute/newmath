import BEDC.Derived.PolishspaceUp.RootCauchyBasisCarrier
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishspaceRootCountableDenseCauchyReadback [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger alignment transport route provenance
      localName cauchyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishspaceRootCauchyBasisCarrier metric complete separable stream readback ledger alignment
        transport route provenance localName bundle pkg ->
      Cont readback alignment cauchyRead ->
        PkgSig bundle localName pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row metric ∨ hsame row stream ∨ hsame row readback ∨
                  hsame row alignment ∨ hsame row cauchyRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory cauchyRead ∧ Cont readback alignment cauchyRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier readbackAlignmentCauchy localNamePkg
  obtain ⟨metricUnary, _completeUnary, _separableUnary, streamUnary, readbackUnary,
    _ledgerUnary, alignmentUnary, _transportUnary, _localNameUnary, _metricCompleteAlignment,
    _alignmentStreamReadback, _ledgerTransportRoute, provenancePkg⟩ := carrier
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed readbackUnary alignmentUnary readbackAlignmentCauchy
  have sourceCauchy :
      (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row) cauchyRead := by
    exact ⟨hsame_refl cauchyRead, cauchyUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row cauchyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row stream ∨ hsame row readback ∨
              hsame row alignment ∨ hsame row cauchyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cauchyRead sourceCauchy
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, cauchyUnary, readbackAlignmentCauchy, provenancePkg, localNamePkg⟩

end BEDC.Derived.PolishspaceUp
