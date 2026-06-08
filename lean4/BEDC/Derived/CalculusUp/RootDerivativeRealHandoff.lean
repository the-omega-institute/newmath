import BEDC.Derived.CalculusUp.RootRealSealNonescape

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootDerivativeRealHandoff [AskSetup] [PackageSetup]
    {C D Q Y R H _T P N graphRead derivativeRead dyadicRead realRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory Q →
          UnaryHistory Y →
            UnaryHistory R →
              UnaryHistory N →
                Cont C D graphRead →
                  Cont graphRead D derivativeRead →
                    Cont derivativeRead Q dyadicRead →
                      Cont dyadicRead R realRead →
                        Cont realRead N namedRead →
                          hsame H (append P N) →
                            PkgSig bundle P pkg →
                              PkgSig bundle namedRead pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row C ∨ hsame row D ∨ hsame row Q ∨
                                        hsame row Y ∨ hsame row R ∨ hsame row namedRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont C D graphRead ∧
                                        Cont graphRead D derivativeRead ∧
                                          Cont derivativeRead Q dyadicRead ∧
                                            Cont dyadicRead R realRead ∧
                                              Cont realRead N namedRead ∧
                                                hsame H (append P N) ∧
                                                  PkgSig bundle P pkg ∧
                                                    PkgSig bundle namedRead pkg)
                                    hsame ∧
                                  UnaryHistory derivativeRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro cUnary dUnary qUnary _yUnary rUnary nUnary graphRoute derivativeRoute dyadicRoute
    realRoute namedRoute transportSame provenancePkg namedPkg
  have graphUnary : UnaryHistory graphRead :=
    unary_cont_closed cUnary dUnary graphRoute
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed graphUnary dUnary derivativeRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed derivativeUnary qUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary rUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row Q ∨ hsame row Y ∨ hsame row R ∨
              hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D graphRead ∧ Cont graphRead D derivativeRead ∧
              Cont derivativeRead Q dyadicRead ∧ Cont dyadicRead R realRead ∧
                Cont realRead N namedRead ∧ hsame H (append P N) ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle namedRead pkg)
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
        ⟨source.right, graphRoute, derivativeRoute, dyadicRoute, realRoute, namedRoute,
          transportSame, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, derivativeUnary, namedUnary⟩

end BEDC.Derived.CalculusUp
