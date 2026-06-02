import BEDC.Derived.SeparatedCompletionUp

namespace BEDC.Derived.SeparatedCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SeparatedCompletionDenseFactorization [AskSetup] [PackageSetup]
    {M D C Z U H R T P N denseRead handoffRead separatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SeparatedCompletionCarrier M D C Z U H R T P N bundle pkg ->
      Cont M D denseRead ->
        Cont denseRead C handoffRead ->
          Cont handoffRead Z separatedRead ->
            PkgSig bundle separatedRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨
                      hsame row U ∨ hsame row denseRead ∨ hsame row handoffRead ∨
                        hsame row separatedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont M D denseRead ∧
                      Cont denseRead C handoffRead ∧ Cont handoffRead Z separatedRead ∧
                        PkgSig bundle separatedRead pkg)
                  hsame ∧
                UnaryHistory denseRead ∧ UnaryHistory handoffRead ∧
                  UnaryHistory separatedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame
  intro carrier denseRoute handoffRoute separatedRoute separatedPkg
  obtain ⟨metricUnary, denseUnary, completionUnary, classifierUnary, _uniqueUnary,
    _transportUnary, _replayUnary, _ledgerUnary, _provenanceUnary, _nameRowUnary,
    _metricDenseCompletion, _completionClassifierUnique, _uniqueTransportReplay,
    _replayLedgerNameRow, _provenancePkg, _nameRowPkg⟩ := carrier
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed metricUnary denseUnary denseRoute
  have handoffReadUnary : UnaryHistory handoffRead :=
    unary_cont_closed denseReadUnary completionUnary handoffRoute
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed handoffReadUnary classifierUnary separatedRoute
  have sourceSeparatedRead :
      (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row) separatedRead := by
    exact ⟨hsame_refl separatedRead, separatedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row D ∨ hsame row C ∨ hsame row Z ∨
              hsame row U ∨ hsame row denseRead ∨ hsame row handoffRead ∨
                hsame row separatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M D denseRead ∧ Cont denseRead C handoffRead ∧
              Cont handoffRead Z separatedRead ∧ PkgSig bundle separatedRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro separatedRead sourceSeparatedRead
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, denseRoute, handoffRoute, separatedRoute, separatedPkg⟩
    }
  exact ⟨cert, denseReadUnary, handoffReadUnary, separatedReadUnary⟩

end BEDC.Derived.SeparatedCompletionUp
