import BEDC.Derived.PolishspaceUp.CompletionDensityHandoff

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceCarrier_l10_consumer_boundary [AskSetup] [PackageSetup]
    {M K D S R W H C G N boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier M K D S R W H C G N bundle pkg →
      Cont W C boundaryRead →
        PkgSig bundle boundaryRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row boundaryRead ∧
                  BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier
                    M K D S R W H C G N bundle pkg)
              (fun row : BHist =>
                hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
                  hsame row R ∨ hsame row W ∨ hsame row boundaryRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle G pkg ∧
                  PkgSig bundle boundaryRead pkg)
              hsame ∧
            UnaryHistory boundaryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier ledgerReplayBoundary boundaryPkg
  have carrierRows :
      BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier
        M K D S R W H C G N bundle pkg := carrier
  obtain ⟨_MUnary, _KUnary, _DUnary, _SUnary, _RUnary, WUnary, _HUnary,
    CUnary, _GUnary, _NUnary, _metricCompleteLedger, _ledgerStreamReadback,
    _transportReplayProvenance, carrierPkg, _localPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed WUnary CUnary ledgerReplayBoundary
  have sourceBoundary :
      (fun row : BHist =>
        hsame row boundaryRead ∧
          BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier
            M K D S R W H C G N bundle pkg) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, carrierRows⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row boundaryRead ∧
              BEDC.Derived.PolishSpaceUp.PolishSpaceCarrier
                M K D S R W H C G N bundle pkg)
          (fun row : BHist =>
            hsame row M ∨ hsame row K ∨ hsame row D ∨ hsame row S ∨
              hsame row R ∨ hsame row W ∨ hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle G pkg ∧ PkgSig bundle boundaryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro row source
      exact ⟨unary_transport boundaryUnary (hsame_symm source.left), carrierPkg,
        boundaryPkg⟩
  }
  exact ⟨cert, boundaryUnary⟩

end BEDC.Derived.PolishspaceUp
