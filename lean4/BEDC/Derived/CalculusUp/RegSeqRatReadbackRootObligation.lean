import BEDC.Derived.CalculusUp.RegSeqRatDyadicErrorRoute

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRegSeqRatReadbackRootObligation [AskSetup] [PackageSetup]
    {R L C D I Q Y H T P N limitRead derivativeRead integralRead limitDyadic
      derivativeDyadic integralDyadic limitSeal derivativeSeal integralSeal namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory D →
        UnaryHistory I →
          UnaryHistory Q →
            UnaryHistory Y →
              UnaryHistory R →
                UnaryHistory N →
                  Cont L Q limitRead →
                    Cont D Q derivativeRead →
                      Cont I Q integralRead →
                        Cont limitRead Y limitDyadic →
                          Cont derivativeRead Y derivativeDyadic →
                            Cont integralRead Y integralDyadic →
                              Cont limitDyadic R limitSeal →
                                Cont derivativeDyadic R derivativeSeal →
                                  Cont integralDyadic R integralSeal →
                                    Cont limitSeal N namedRead →
                                      PkgSig bundle P pkg →
                                        PkgSig bundle N pkg →
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                (hsame row limitSeal ∨
                                                    hsame row derivativeSeal ∨
                                                      hsame row integralSeal ∨
                                                        hsame row namedRead) ∧
                                                  UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row limitSeal ∨
                                                  hsame row derivativeSeal ∨
                                                    hsame row integralSeal ∨
                                                      hsame row namedRead ∨
                                                        hsame row L ∨ hsame row C ∨
                                                          hsame row D ∨ hsame row I ∨
                                                            hsame row Q ∨ hsame row Y ∨
                                                              hsame row H ∨ hsame row T ∨
                                                                hsame row R ∨ hsame row N)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧ Cont L Q limitRead ∧
                                                  Cont D Q derivativeRead ∧
                                                    Cont I Q integralRead ∧
                                                      Cont limitRead Y limitDyadic ∧
                                                        Cont derivativeRead Y derivativeDyadic ∧
                                                          Cont integralRead Y integralDyadic ∧
                                                            Cont limitDyadic R limitSeal ∧
                                                              Cont derivativeDyadic R
                                                                  derivativeSeal ∧
                                                                Cont integralDyadic R
                                                                    integralSeal ∧
                                                                  Cont limitSeal N
                                                                      namedRead ∧
                                                                    PkgSig bundle P pkg ∧
                                                                      PkgSig bundle N pkg)
                                              hsame ∧
                                            UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro lUnary dUnary iUnary qUnary yUnary rUnary nUnary limitRoute derivativeRoute
    integralRoute limitDyadicRoute derivativeDyadicRoute integralDyadicRoute limitSealRoute
    derivativeSealRoute integralSealRoute namedRoute provenancePkg namedPkg
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed lUnary qUnary limitRoute
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed dUnary qUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed iUnary qUnary integralRoute
  have limitDyadicUnary : UnaryHistory limitDyadic :=
    unary_cont_closed limitReadUnary yUnary limitDyadicRoute
  have derivativeDyadicUnary : UnaryHistory derivativeDyadic :=
    unary_cont_closed derivativeReadUnary yUnary derivativeDyadicRoute
  have integralDyadicUnary : UnaryHistory integralDyadic :=
    unary_cont_closed integralReadUnary yUnary integralDyadicRoute
  have limitSealUnary : UnaryHistory limitSeal :=
    unary_cont_closed limitDyadicUnary rUnary limitSealRoute
  have derivativeSealUnary : UnaryHistory derivativeSeal :=
    unary_cont_closed derivativeDyadicUnary rUnary derivativeSealRoute
  have integralSealUnary : UnaryHistory integralSeal :=
    unary_cont_closed integralDyadicUnary rUnary integralSealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed limitSealUnary nUnary namedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro namedRead
            ⟨Or.inr (Or.inr (Or.inr (hsame_refl namedRead))), namedUnary⟩
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
          constructor
          · cases source.left with
            | inl limitSame =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) limitSame)
            | inr rest =>
                cases rest with
                | inl derivativeSame =>
                    exact Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) derivativeSame))
                | inr rest =>
                    cases rest with
                    | inl integralSame =>
                        exact Or.inr
                          (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) integralSame)))
                    | inr namedSame =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) namedSame)))
          · exact unary_transport source.right sameRows
      }
      pattern_sound := by
        intro _row source
        cases source.left with
        | inl limitSame =>
            exact Or.inl limitSame
        | inr rest =>
            cases rest with
            | inl derivativeSame =>
                exact Or.inr (Or.inl derivativeSame)
            | inr rest =>
                cases rest with
                | inl integralSame =>
                    exact Or.inr (Or.inr (Or.inl integralSame))
                | inr namedSame =>
                    exact Or.inr (Or.inr (Or.inr (Or.inl namedSame)))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, limitRoute, derivativeRoute, integralRoute, limitDyadicRoute,
            derivativeDyadicRoute, integralDyadicRoute, limitSealRoute, derivativeSealRoute,
            integralSealRoute, namedRoute, provenancePkg, namedPkg⟩
    }
  · exact namedUnary

end BEDC.Derived.CalculusUp
