import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCompleteSeparableSynthesis [AskSetup] [PackageSetup]
    {M K D S R W H C G N completionRead denseRead synthesisRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg →
      Cont M K completionRead →
        Cont M D denseRead →
          Cont completionRead denseRead synthesisRead →
            PkgSig bundle synthesisRead pkg →
              SemanticNameCert
                    (fun row : BHist =>
                      (hsame row completionRead ∨ hsame row denseRead ∨
                          hsame row synthesisRead) ∧
                        UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                        hsame row R ∨ hsame row W ∨ hsame row completionRead ∨
                          hsame row denseRead ∨ hsame row synthesisRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle G pkg ∧
                        PkgSig bundle synthesisRead pkg)
                    hsame ∧
                UnaryHistory completionRead ∧ UnaryHistory denseRead ∧
                  UnaryHistory synthesisRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier completionRoute denseRoute synthesisRoute synthesisPkg
  obtain ⟨MUnary, KUnary, DUnary, _SUnary, _RUnary, _WUnary, _HUnary, _CUnary,
    _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, carrierPkg, _localPkg⟩ := carrier
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed MUnary KUnary completionRoute
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed MUnary DUnary denseRoute
  have synthesisUnary : UnaryHistory synthesisRead :=
    unary_cont_closed completionUnary denseUnary synthesisRoute
  have sourceSynthesis :
      (fun row : BHist =>
        (hsame row completionRead ∨ hsame row denseRead ∨ hsame row synthesisRead) ∧
          UnaryHistory row) synthesisRead := by
    exact ⟨Or.inr (Or.inr (hsame_refl synthesisRead)), synthesisUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row completionRead ∨ hsame row denseRead ∨ hsame row synthesisRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
              hsame row R ∨ hsame row W ∨ hsame row completionRead ∨
                hsame row denseRead ∨ hsame row synthesisRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle G pkg ∧ PkgSig bundle synthesisRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro synthesisRead sourceSynthesis
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
        have shifted :
            hsame _other completionRead ∨ hsame _other denseRead ∨
              hsame _other synthesisRead := by
          cases source.left with
          | inl sameCompletion =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameCompletion)
          | inr rest =>
              cases rest with
              | inl sameDense =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameDense))
              | inr sameSynthesis =>
                  exact Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameSynthesis))
        exact ⟨shifted, unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCompletion =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameCompletion))))))
      | inr rest =>
          cases rest with
          | inl sameDense =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDense)))))))
          | inr sameSynthesis =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameSynthesis)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, carrierPkg, synthesisPkg⟩
  }
  exact ⟨cert, completionUnary, denseUnary, synthesisUnary⟩

end BEDC.Derived.PolishspaceUp
