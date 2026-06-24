import BEDC.Derived.CauchyCompletionOperatorUp.LedgerNonescape

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionOperatorFunctorialHandoff [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead windowRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorPacket M B U S R D Q E H C P N bundle pkg →
      Cont M U boundaryRead →
        Cont boundaryRead S windowRead →
          Cont windowRead E sealRead →
            PkgSig bundle sealRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row M ∨ hsame row U ∨ hsame row B ∨ hsame row S ∨
                      hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row E ∨
                        hsame row sealRead)
                  (fun row : BHist =>
                    hsame row sealRead ∧ Cont M U boundaryRead ∧
                      Cont boundaryRead S windowRead ∧ Cont windowRead E sealRead ∧
                        PkgSig bundle sealRead pkg)
                  hsame ∧
                UnaryHistory boundaryRead ∧ UnaryHistory windowRead ∧
                  UnaryHistory sealRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet metricUniformBoundary boundaryWindow windowSeal sealPkg
  obtain ⟨metricUnary, _boundaryUnary, uniformUnary, streamUnary, _regularUnary,
    _dyadicUnary, _separatedUnary, realSealUnary, _transportUnary, _replayUnary,
    provenanceUnary, _nameUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    provenancePkg, _namePkg⟩ := packet
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed metricUnary uniformUnary metricUniformBoundary
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed boundaryUnary streamUnary boundaryWindow
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary realSealUnary windowSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row U ∨ hsame row B ∨ hsame row S ∨ hsame row R ∨
              hsame row D ∨ hsame row Q ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            hsame row sealRead ∧ Cont M U boundaryRead ∧
              Cont boundaryRead S windowRead ∧ Cont windowRead E sealRead ∧
                PkgSig bundle sealRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead sourceSeal
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          sourceRow.left)))))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, metricUniformBoundary, boundaryWindow, windowSeal, sealPkg⟩
  }
  exact ⟨cert, boundaryUnary, windowUnary, sealUnary, provenancePkg⟩

end BEDC.Derived.CauchyCompletionOperatorUp
