import BEDC.Derived.CauchyCompletionMinimalityUp.DenseImageCoverage

namespace BEDC.Derived.CauchyCompletionMinimalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMinimalitySeparatedReflectionRoute [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      denseRead comparedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg →
      Cont completion embedding denseRead →
        Cont extension separated comparedRead →
          SemanticNameCert
              (fun row : BHist => hsame row comparedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row embedding ∨ hsame row universal ∨ hsame row extension ∨
                  hsame row separated ∨ hsame row comparedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont completion embedding denseRead ∧
                  Cont extension separated comparedRead ∧ PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory denseRead ∧ UnaryHistory comparedRead := by
  -- BEDC touchpoint anchor: CauchyCompletionMinimalityCarrier BHist ProbeBundle Pkg Cont
  intro carrier denseRoute comparedRoute
  obtain ⟨_sourceUnary, completionUnary, embeddingUnary, _universalUnary, extensionUnary,
    separatedUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _universalRoute, _separatedRoute, provenancePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed completionUnary embeddingUnary denseRoute
  have comparedUnary : UnaryHistory comparedRead :=
    unary_cont_closed extensionUnary separatedUnary comparedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row comparedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row embedding ∨ hsame row universal ∨ hsame row extension ∨
              hsame row separated ∨ hsame row comparedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completion embedding denseRead ∧
              Cont extension separated comparedRead ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro comparedRead ⟨hsame_refl comparedRead, comparedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, denseRoute, comparedRoute, provenancePkg⟩
  }
  exact ⟨cert, denseUnary, comparedUnary⟩

end BEDC.Derived.CauchyCompletionMinimalityUp
