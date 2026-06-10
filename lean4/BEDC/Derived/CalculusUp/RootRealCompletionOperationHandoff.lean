import BEDC.Derived.CalculusUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootRealCompletionOperationHandoff [AskSetup] [PackageSetup]
    {C D I L R Q Y _H _T P N derivativeRead integralRead limitRead derivativeSeal
      integralSeal limitSeal namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory I →
          UnaryHistory L →
            UnaryHistory Q →
              UnaryHistory Y →
                UnaryHistory R →
                  UnaryHistory N →
                    Cont C D derivativeRead →
                      Cont C I integralRead →
                        Cont C L limitRead →
                          Cont derivativeRead Q derivativeSeal →
                            Cont integralRead Q integralSeal →
                              Cont limitRead Q limitSeal →
                                Cont Q Y namedRead →
                                  PkgSig bundle P pkg →
                                    PkgSig bundle N pkg →
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            (hsame row derivativeSeal ∨
                                                hsame row integralSeal ∨
                                                  hsame row limitSeal ∨
                                                    hsame row namedRead) ∧
                                              UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row C ∨ hsame row D ∨ hsame row I ∨
                                              hsame row L ∨ hsame row Q ∨ hsame row Y ∨
                                                hsame row R ∨ hsame row N ∨
                                                  hsame row derivativeSeal ∨
                                                    hsame row integralSeal ∨
                                                      hsame row limitSeal ∨
                                                        hsame row namedRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont C D derivativeRead ∧
                                              Cont C I integralRead ∧ Cont C L limitRead ∧
                                                Cont derivativeRead Q derivativeSeal ∧
                                                  Cont integralRead Q integralSeal ∧
                                                    Cont limitRead Q limitSeal ∧
                                                      Cont Q Y namedRead ∧
                                                        PkgSig bundle P pkg ∧
                                                          PkgSig bundle N pkg)
                                          hsame ∧
                                        UnaryHistory derivativeRead ∧
                                          UnaryHistory integralRead ∧
                                            UnaryHistory limitRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro cUnary dUnary iUnary lUnary qUnary yUnary _rUnary _nUnary derivativeRoute
    integralRoute limitRoute derivativeSealRoute integralSealRoute limitSealRoute namedRoute
    provenancePkg namePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed cUnary dUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed cUnary iUnary integralRoute
  have limitReadUnary : UnaryHistory limitRead :=
    unary_cont_closed cUnary lUnary limitRoute
  have derivativeSealUnary : UnaryHistory derivativeSeal :=
    unary_cont_closed derivativeReadUnary qUnary derivativeSealRoute
  have integralSealUnary : UnaryHistory integralSeal :=
    unary_cont_closed integralReadUnary qUnary integralSealRoute
  have limitSealUnary : UnaryHistory limitSeal :=
    unary_cont_closed limitReadUnary qUnary limitSealRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed qUnary yUnary namedRoute
  have derivativeSource :
      (fun row : BHist =>
        (hsame row derivativeSeal ∨ hsame row integralSeal ∨ hsame row limitSeal ∨
            hsame row namedRead) ∧
          UnaryHistory row) derivativeSeal := by
    exact ⟨Or.inl (hsame_refl derivativeSeal), derivativeSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row derivativeSeal ∨ hsame row integralSeal ∨ hsame row limitSeal ∨
                hsame row namedRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨ hsame row Q ∨
              hsame row Y ∨ hsame row R ∨ hsame row N ∨ hsame row derivativeSeal ∨
                hsame row integralSeal ∨ hsame row limitSeal ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D derivativeRead ∧ Cont C I integralRead ∧
              Cont C L limitRead ∧ Cont derivativeRead Q derivativeSeal ∧
                Cont integralRead Q integralSeal ∧ Cont limitRead Q limitSeal ∧
                  Cont Q Y namedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro derivativeSeal derivativeSource
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
          | inl derivativeSame =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) derivativeSame)
          | inr rest =>
              cases rest with
              | inl integralSame =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) integralSame))
              | inr rest' =>
                  cases rest' with
                  | inl limitSame =>
                      exact
                        Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) limitSame)))
                  | inr namedSame =>
                      exact
                        Or.inr
                          (Or.inr
                            (Or.inr (hsame_trans (hsame_symm sameRows) namedSame)))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl derivativeSame =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inl derivativeSame))))))))
      | inr rest =>
          cases rest with
          | inl integralSame =>
              exact
                Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr (Or.inl integralSame)))))))))
          | inr rest' =>
              cases rest' with
              | inl limitSame =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inl limitSame))))))))))
              | inr namedSame =>
                  exact
                    Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr namedSame))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, derivativeRoute, integralRoute, limitRoute, derivativeSealRoute,
          integralSealRoute, limitSealRoute, namedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, derivativeReadUnary, integralReadUnary, limitReadUnary⟩

end BEDC.Derived.CalculusUp
