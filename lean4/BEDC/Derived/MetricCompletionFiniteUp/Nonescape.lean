import BEDC.Derived.MetricCompletionFiniteUp.NameCertObligations

namespace BEDC.Derived.MetricCompletionFiniteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletionFiniteNonescape [AskSetup] [PackageSetup]
    {metric cauchyBasis window embedding readback selector transport replay provenance localName
      sourceRead finiteRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionFiniteCarrier metric cauchyBasis window embedding readback selector transport
        replay provenance localName bundle pkg →
      Cont metric cauchyBasis sourceRead →
        Cont window embedding finiteRead →
          SemanticNameCert
              (fun row : BHist => hsame row finiteRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row metric ∨ hsame row cauchyBasis ∨ hsame row window ∨
                  hsame row embedding ∨ hsame row readback ∨ hsame row selector ∨
                    hsame row finiteRead ∨ hsame row localName)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont metric cauchyBasis sourceRead ∧
                  Cont window embedding finiteRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory sourceRead ∧ UnaryHistory finiteRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier sourceRoute finiteRoute
  obtain ⟨metricUnary, basisUnary, windowUnary, embeddingUnary, _readbackUnary,
    _selectorUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    provenancePkg, localNamePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed metricUnary basisUnary sourceRoute
  have finiteReadUnary : UnaryHistory finiteRead :=
    unary_cont_closed windowUnary embeddingUnary finiteRoute
  have finiteSource :
      (fun row : BHist => hsame row finiteRead ∧ UnaryHistory row) finiteRead := by
    exact ⟨hsame_refl finiteRead, finiteReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row finiteRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row cauchyBasis ∨ hsame row window ∨
              hsame row embedding ∨ hsame row readback ∨ hsame row selector ∨
                hsame row finiteRead ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont metric cauchyBasis sourceRead ∧
              Cont window embedding finiteRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro finiteRead finiteSource
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, finiteRoute, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, sourceReadUnary, finiteReadUnary⟩

end BEDC.Derived.MetricCompletionFiniteUp
