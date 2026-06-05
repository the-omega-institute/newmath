import BEDC.Derived.SeparatedCompletionUp.DenseFactorization

namespace BEDC.Derived.SeparatedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedCompletionZeroDistanceFactorization [AskSetup] [PackageSetup]
    {M D C Z U H R T P N denseRead handoffRead separatedRead zeroRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedCompletionCarrier M D C Z U H R T P N bundle pkg ->
      Cont M D denseRead ->
        Cont denseRead C handoffRead ->
          Cont handoffRead Z separatedRead ->
            Cont separatedRead U zeroRead ->
              PkgSig bundle zeroRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨
                        hsame row U ∨ hsame row separatedRead ∨ hsame row zeroRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M D denseRead ∧
                        Cont denseRead C handoffRead ∧ Cont handoffRead Z separatedRead ∧
                          Cont separatedRead U zeroRead ∧ PkgSig bundle zeroRead pkg)
                    hsame ∧ UnaryHistory denseRead ∧ UnaryHistory handoffRead ∧
                  UnaryHistory separatedRead ∧ UnaryHistory zeroRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier denseRoute handoffRoute separatedRoute zeroRoute zeroPkg
  obtain ⟨metricUnary, denseUnary, completionUnary, classifierUnary, uniqueUnary,
    _transportUnary, _replayUnary, _ledgerUnary, _provenanceUnary, _nameRowUnary,
    _metricDenseCompletion, _completionClassifierUnique, _uniqueTransportReplay,
    _replayLedgerNameRow, _provenancePkg, _nameRowPkg⟩ := carrier
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary denseUnary denseRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed denseReadUnary completionUnary handoffRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed handoffReadUnary classifierUnary separatedRoute
  have zeroReadUnary : UnaryHistory zeroRead :=
    unary_cont_closed separatedReadUnary uniqueUnary zeroRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨ hsame row U ∨
              hsame row separatedRead ∨ hsame row zeroRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M D denseRead ∧ Cont denseRead C handoffRead ∧
              Cont handoffRead Z separatedRead ∧ Cont separatedRead U zeroRead ∧
                PkgSig bundle zeroRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zeroRead
        ⟨hsame_refl zeroRead, zeroReadUnary⟩
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
      exact ⟨source.right, denseRoute, handoffRoute, separatedRoute, zeroRoute, zeroPkg⟩
  }
  exact ⟨cert, denseReadUnary, handoffReadUnary, separatedReadUnary, zeroReadUnary⟩

end BEDC.Derived.SeparatedCompletionUp
