import BEDC.Derived.CalculusUp.RootL10Nonescape

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootRealSealNonescape [AskSetup] [PackageSetup]
    {C D I L R Q Y H T P N derivativeRead integralRead limitRead dyadicRead realRead
      namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory I →
          UnaryHistory L →
            UnaryHistory R →
              UnaryHistory Q →
                UnaryHistory Y →
                  UnaryHistory N →
                    Cont D Q derivativeRead →
                      Cont I Q integralRead →
                        Cont L Q limitRead →
                          Cont Q Y dyadicRead →
                            Cont dyadicRead R realRead →
                              Cont realRead N namedRead →
                                PkgSig bundle P pkg →
                                  PkgSig bundle namedRead pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row namedRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row D ∨ hsame row I ∨ hsame row L ∨
                                            hsame row Q ∨ hsame row Y ∨ hsame row R ∨
                                              hsame row namedRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont Q Y dyadicRead ∧
                                            Cont dyadicRead R realRead ∧
                                              Cont realRead N namedRead ∧
                                                PkgSig bundle P pkg ∧
                                                  PkgSig bundle namedRead pkg)
                                        hsame ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _cUnary _dUnary _iUnary _lUnary rUnary qUnary yUnary nUnary _derivativeRoute
    _integralRoute _limitRoute dyadicRoute realRoute namedRoute provenancePkg namedPkg
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed qUnary yUnary dyadicRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed dyadicUnary rUnary realRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed realUnary nUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
                    (Or.inr source.left)))))
      ledger_sound := by
        intro _row source
        exact ⟨source.right, dyadicRoute, realRoute, namedRoute, provenancePkg, namedPkg⟩
    }
  · exact namedUnary

end BEDC.Derived.CalculusUp
