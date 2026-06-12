import BEDC.Derived.CalculusUp.RootRealSealNonescape

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootLimitNonescape [AskSetup] [PackageSetup]
    {C L Q Y R H T P N limitRead dyadicRead sealRead structuralRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory L →
        UnaryHistory Q →
          UnaryHistory Y →
            UnaryHistory R →
              UnaryHistory H →
                UnaryHistory T →
                  UnaryHistory N →
                    Cont C L limitRead →
                      Cont limitRead Q dyadicRead →
                        Cont dyadicRead R sealRead →
                          Cont H T structuralRead →
                            Cont sealRead N namedRead →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row C ∨ hsame row L ∨ hsame row Q ∨
                                          hsame row Y ∨ hsame row R ∨ hsame row H ∨
                                            hsame row T ∨ hsame row N ∨
                                              hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont C L limitRead ∧
                                          Cont limitRead Q dyadicRead ∧
                                            Cont dyadicRead R sealRead ∧
                                              Cont H T structuralRead ∧
                                                Cont sealRead N namedRead ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory limitRead ∧ UnaryHistory dyadicRead ∧
                                      UnaryHistory sealRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro cUnary lUnary qUnary _yUnary rUnary hUnary tUnary nUnary limitRoute dyadicRoute
    sealRoute structuralRoute namedRoute provenancePkg namePkg
  have limitUnary : UnaryHistory limitRead :=
    unary_cont_closed cUnary lUnary limitRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed limitUnary qUnary dyadicRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed dyadicUnary rUnary sealRoute
  have _structuralUnary : UnaryHistory structuralRead :=
    unary_cont_closed hUnary tUnary structuralRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed sealUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row L ∨ hsame row Q ∨ hsame row Y ∨ hsame row R ∨
              hsame row H ∨ hsame row T ∨ hsame row N ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C L limitRead ∧ Cont limitRead Q dyadicRead ∧
              Cont dyadicRead R sealRead ∧ Cont H T structuralRead ∧
                Cont sealRead N namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, limitRoute, dyadicRoute, sealRoute, structuralRoute,
          namedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, limitUnary, dyadicUnary, sealUnary, namedUnary⟩

end BEDC.Derived.CalculusUp
