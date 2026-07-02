import BEDC.Derived.AbelSummationUp.PartialSumHandoff

namespace BEDC.Derived.AbelSummationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AbelSummationDirichletTestRoute [AskSetup] [PackageSetup]
    {S A D B T R E H C P N identityRead testRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory A →
        UnaryHistory D →
          UnaryHistory B →
            UnaryHistory T →
              UnaryHistory R →
                UnaryHistory P →
                  Cont S A D →
                    Cont D B T →
                      Cont T R identityRead →
                        Cont identityRead P namedRead →
                          PkgSig bundle namedRead pkg →
                            SemanticNameCert
                                (fun row : BHist =>
                                  hsame row namedRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row S ∨ hsame row A ∨ hsame row D ∨
                                    hsame row B ∨ hsame row T ∨ hsame row R ∨
                                      hsame row E ∨ hsame row H ∨ hsame row C ∨
                                        hsame row P ∨ hsame row N ∨
                                          hsame row identityRead ∨
                                            hsame row namedRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S A D ∧ Cont D B T ∧
                                    Cont T R identityRead ∧
                                      Cont identityRead P namedRead ∧
                                        PkgSig bundle namedRead pkg)
                                hsame ∧ UnaryHistory identityRead ∧
                              UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro _sUnary _aUnary dUnary bUnary tUnary rUnary pUnary sourceRoute boundaryRoute
    identityRoute namedRoute namedPkg
  have identityUnary : UnaryHistory identityRead :=
    unary_cont_closed tUnary rUnary identityRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed identityUnary pUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row A ∨ hsame row D ∨ hsame row B ∨
              hsame row T ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row identityRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S A D ∧ Cont D B T ∧ Cont T R identityRead ∧
              Cont identityRead P namedRead ∧ PkgSig bundle namedRead pkg)
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
      repeat (first | exact source.left | apply Or.inr)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, boundaryRoute, identityRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, identityUnary, namedUnary⟩

end BEDC.Derived.AbelSummationUp
