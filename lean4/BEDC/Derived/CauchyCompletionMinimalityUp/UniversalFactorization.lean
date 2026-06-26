import BEDC.Derived.CauchyCompletionMinimalityUp.DenseImageCoverage

namespace BEDC.Derived.CauchyCompletionMinimalityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionMinimalityCarrier_universal_factorization [AskSetup] [PackageSetup]
    {source completion embedding universal extension separated transport replay provenance name
      denseRead universalRead extensionRead compared : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionMinimalityCarrier source completion embedding universal extension separated
        transport replay provenance name bundle pkg ->
      Cont completion embedding denseRead ->
        Cont denseRead universal universalRead ->
          Cont universalRead extension extensionRead ->
            Cont extension separated compared ->
              PkgSig bundle name pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row compared ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
                        hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                          hsame row compared)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont completion embedding denseRead ∧
                        Cont denseRead universal universalRead ∧
                          Cont universalRead extension extensionRead ∧
                            Cont extension separated compared ∧ PkgSig bundle provenance pkg ∧
                              PkgSig bundle name pkg)
                    hsame ∧
                  UnaryHistory denseRead ∧ UnaryHistory universalRead ∧
                    UnaryHistory extensionRead ∧ UnaryHistory compared := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute universalRoute extensionRoute comparedRoute namePkg
  obtain ⟨sourceUnary, completionUnary, embeddingUnary, universalUnary, extensionUnary,
    separatedUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary,
    _carrierUniversalRoute, _carrierSeparatedRoute, provenancePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed completionUnary embeddingUnary denseRoute
  have universalReadUnary : UnaryHistory universalRead :=
    unary_cont_closed denseUnary universalUnary universalRoute
  have extensionReadUnary : UnaryHistory extensionRead :=
    unary_cont_closed universalReadUnary extensionUnary extensionRoute
  have comparedUnary : UnaryHistory compared :=
    unary_cont_closed extensionUnary separatedUnary comparedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compared ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row completion ∨ hsame row embedding ∨
              hsame row universal ∨ hsame row extension ∨ hsame row separated ∨
                hsame row compared)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont completion embedding denseRead ∧
              Cont denseRead universal universalRead ∧ Cont universalRead extension extensionRead ∧
                Cont extension separated compared ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle name pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compared ⟨hsame_refl compared, comparedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseRoute, universalRoute, extensionRoute, comparedRoute,
          provenancePkg, namePkg⟩
  }
  exact ⟨cert, denseUnary, universalReadUnary, extensionReadUnary, comparedUnary⟩

end BEDC.Derived.CauchyCompletionMinimalityUp
