import BEDC.Derived.CauchyCompletionOperatorUp.FunctorialHandoff

namespace BEDC.Derived.CauchyCompletionOperatorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionOperatorWindowExtraction [AskSetup] [PackageSetup]
    {M B U S R D Q E H C P N finiteWindow separatedRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionOperatorLedgerPacket M B U S R D Q E H C P N bundle pkg →
      Cont B S finiteWindow →
        Cont finiteWindow R D →
          Cont D Q separatedRead →
            Cont separatedRead E sealRead →
              PkgSig bundle sealRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row B ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨
                        hsame row Q ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row finiteWindow ∨
                            hsame row separatedRead ∨ hsame row sealRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont B S finiteWindow ∧
                        Cont finiteWindow R D ∧ Cont D Q separatedRead ∧
                          Cont separatedRead E sealRead ∧ PkgSig bundle sealRead pkg)
                    hsame ∧
                  UnaryHistory finiteWindow ∧ UnaryHistory separatedRead ∧
                    UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro packet boundaryWindow windowReadback dyadicSeparated separatedSeal sealPkg
  obtain ⟨_metricUnary, boundaryUnary, _uniformUnary, streamUnary, regularUnary,
    dyadicUnary, separatedUnary, realSealUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameUnary, _streamRegularDyadic, _dyadicSeparatedReal,
    _provenancePkg, _namePkg⟩ := packet
  have finiteUnary : UnaryHistory finiteWindow :=
    unary_cont_closed boundaryUnary streamUnary boundaryWindow
  have separatedReadUnary : UnaryHistory separatedRead :=
    unary_cont_closed dyadicUnary separatedUnary dyadicSeparated
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed separatedReadUnary realSealUnary separatedSeal
  have sourceSeal :
      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row) sealRead := by
    exact ⟨hsame_refl sealRead, sealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row Q ∨
              hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row finiteWindow ∨ hsame row separatedRead ∨
                  hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B S finiteWindow ∧ Cont finiteWindow R D ∧
              Cont D Q separatedRead ∧ Cont separatedRead E sealRead ∧
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact sourceRow.left
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, boundaryWindow, windowReadback, dyadicSeparated, separatedSeal,
          sealPkg⟩
  }
  exact ⟨cert, finiteUnary, separatedReadUnary, sealUnary⟩

end BEDC.Derived.CauchyCompletionOperatorUp
