import BEDC.Derived.SequentiallyCompleteMetricUp.DisplayedLimitUniqueness

namespace BEDC.Derived.SequentiallyCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentiallyCompleteMetricDisplayedLimitUniquenessRoute [AskSetup] [PackageSetup]
    {X S M L D H C P N uniquenessRead displayRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    sequentiallyCompleteMetricFields (SequentiallyCompleteMetricUp.mk X S M L D H C P N) =
        [X, S, M, L, D, H, C, P, N] ->
      UnaryHistory X ->
        UnaryHistory S ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory D ->
                UnaryHistory C ->
                  UnaryHistory N ->
                    Cont M L uniquenessRead ->
                      Cont uniquenessRead D displayRead ->
                        Cont displayRead C namedRead ->
                          PkgSig bundle P pkg ->
                            PkgSig bundle N pkg ->
                              SemanticNameCert
                                  (fun row : BHist =>
                                    hsame row namedRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row X ∨ hsame row S ∨ hsame row M ∨
                                      hsame row L ∨ hsame row D ∨ hsame row namedRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont M L uniquenessRead ∧
                                      Cont uniquenessRead D displayRead ∧
                                        Cont displayRead C namedRead ∧
                                          PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                  hsame ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fieldRows xUnary sUnary mUnary lUnary dUnary cUnary nUnary uniquenessRoute
    displayRoute namedRoute provenancePkg namePkg
  cases fieldRows
  have uniquenessUnary : UnaryHistory uniquenessRead :=
    unary_cont_closed mUnary lUnary uniquenessRoute
  have displayUnary : UnaryHistory displayRead :=
    unary_cont_closed uniquenessUnary dUnary displayRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed displayUnary cUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row S ∨ hsame row M ∨ hsame row L ∨
              hsame row D ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M L uniquenessRead ∧
              Cont uniquenessRead D displayRead ∧ Cont displayRead C namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, uniquenessRoute, displayRoute, namedRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, namedUnary⟩

end BEDC.Derived.SequentiallyCompleteMetricUp
