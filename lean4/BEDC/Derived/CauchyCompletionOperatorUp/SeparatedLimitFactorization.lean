import BEDC.Derived.CauchyCompletionOperatorUp.WindowExtraction

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionOperatorSeparatedLimitFactorization [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N boundaryRead finiteWindow separatedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg →
      Cont M U boundaryRead →
        Cont B S finiteWindow →
          Cont finiteWindow R D →
            Cont D Q separatedRead →
              PkgSig bundle separatedRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row U ∨ hsame row B ∨ hsame row S ∨
                        hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row H ∨
                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                            hsame row boundaryRead ∨ hsame row finiteWindow ∨
                              hsame row separatedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont M U boundaryRead ∧
                        Cont B S finiteWindow ∧ Cont finiteWindow R D ∧
                          Cont D Q separatedRead ∧ PkgSig bundle separatedRead pkg)
                    hsame ∧
                  UnaryHistory boundaryRead ∧ UnaryHistory finiteWindow ∧
                    UnaryHistory separatedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet metricUniformBoundary boundaryWindow windowReadback dyadicSeparated separatedPkg
  obtain ⟨metricUnary, boundaryUnary, uniformUnary, streamUnary, regularUnary,
    dyadicUnary, separatedUnary, _realSealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have boundaryReadUnary : UnaryHistory boundaryRead :=
    unary_cont_closed metricUnary uniformUnary metricUniformBoundary
  have finiteWindowUnary : UnaryHistory finiteWindow :=
    unary_cont_closed boundaryUnary streamUnary boundaryWindow
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed dyadicUnary separatedUnary dyadicSeparated
  have sourceSeparated :
      (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row) separatedRead := by
    exact ⟨hsame_refl separatedRead, separatedReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row separatedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row U ∨ hsame row B ∨ hsame row S ∨
              hsame row R ∨ hsame row D ∨ hsame row Q ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row boundaryRead ∨ hsame row finiteWindow ∨
                    hsame row separatedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M U boundaryRead ∧ Cont B S finiteWindow ∧
              Cont finiteWindow R D ∧ Cont D Q separatedRead ∧
                PkgSig bundle separatedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro separatedRead sourceSeparated
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
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))))))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, metricUniformBoundary, boundaryWindow, windowReadback,
          dyadicSeparated, separatedPkg⟩
  }
  exact ⟨cert, boundaryReadUnary, finiteWindowUnary, separatedReadUnary⟩

end BEDC.Derived.CauchyCompletionOperatorUp
