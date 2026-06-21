import BEDC.Derived.RegularCauchyDiagonalMeetUp.SharedThresholdFactorization

namespace BEDC.Derived.RegularCauchyDiagonalMeetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyDiagonalMeetObligationClosure [AskSetup] [PackageSetup]
    {T M E W Q H C P N mt te ew thresholdRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M →
      UnaryHistory T →
        UnaryHistory E →
          UnaryHistory W →
            UnaryHistory Q →
              UnaryHistory N →
                Cont M T mt →
                  Cont mt E te →
                    Cont te W ew →
                      Cont ew Q thresholdRead →
                        Cont thresholdRead N namedRead →
                          PkgSig bundle P pkg →
                            PkgSig bundle namedRead pkg →
                              SemanticNameCert
                                  (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row M ∨ hsame row T ∨ hsame row E ∨
                                      hsame row W ∨ hsame row Q ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M T mt ∧ Cont mt E te ∧
                                      Cont te W ew ∧ Cont ew Q thresholdRead ∧
                                        Cont thresholdRead N namedRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
                                  hsame ∧
                                UnaryHistory namedRead ∧
                                  SemanticNameCert
                                    (fun row : BHist => hsame row Q)
                                    (fun row : BHist =>
                                      hsame row T ∨ hsame row M ∨ hsame row E ∨
                                        hsame row W ∨ hsame row Q ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row N)
                                    (fun row : BHist => hsame row Q)
                                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro unaryM unaryT unaryE unaryW unaryQ unaryN mtRoute teRoute ewRoute thresholdRoute
    namedRoute provenancePkg namedPkg
  have shared :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row T ∨ hsame row E ∨ hsame row W ∨
              hsame row Q ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M T mt ∧ Cont mt E te ∧ Cont te W ew ∧
              Cont ew Q thresholdRead ∧ Cont thresholdRead N namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
          hsame ∧
        UnaryHistory namedRead :=
    RegularCauchyDiagonalMeetSharedThresholdFactorization unaryM unaryT unaryE unaryW unaryQ
      (_H := H) (_C := C) unaryN mtRoute teRoute ewRoute thresholdRoute namedRoute
      provenancePkg namedPkg
  have qCert :
      SemanticNameCert
          (fun row : BHist => hsame row Q)
          (fun row : BHist =>
            hsame row T ∨ hsame row M ∨ hsame row E ∨ hsame row W ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row Q)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro Q (hsame_refl Q)
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
          exact hsame_trans (hsame_symm sameRows) sourceRow
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sourceRow))))
      ledger_sound := by
        intro _row sourceRow
        exact sourceRow
    }
  exact ⟨shared.left, shared.right, qCert⟩

end BEDC.Derived.RegularCauchyDiagonalMeetUp
