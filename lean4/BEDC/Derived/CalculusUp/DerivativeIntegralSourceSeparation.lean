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

theorem CalculusDerivativeIntegralSourceSeparation [AskSetup] [PackageSetup]
    {R L C D I Q H T P N derivativeRead integralRead derivativeSeal integralSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory L →
        UnaryHistory C →
          UnaryHistory D →
            UnaryHistory I →
              UnaryHistory Q →
                UnaryHistory H →
                  UnaryHistory T →
                    UnaryHistory P →
                      UnaryHistory N →
                        Cont C D derivativeRead →
                          Cont C I integralRead →
                            Cont derivativeRead Q derivativeSeal →
                              Cont integralRead Q integralSeal →
                                PkgSig bundle P pkg →
                                  PkgSig bundle N pkg →
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          (hsame row derivativeSeal ∨ hsame row integralSeal) ∧
                                            UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row D ∨ hsame row I ∨ hsame row Q ∨
                                            hsame row derivativeSeal ∨ hsame row integralSeal)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                            PkgSig bundle N pkg)
                                        hsame ∧
                                      UnaryHistory derivativeRead ∧
                                        UnaryHistory integralRead ∧
                                          UnaryHistory derivativeSeal ∧
                                            UnaryHistory integralSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro _rUnary _lUnary cUnary dUnary iUnary qUnary _hUnary _tUnary _pUnary _nUnary
    derivativeRoute integralRoute derivativeSealRoute integralSealRoute provenancePkg namePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed cUnary dUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed cUnary iUnary integralRoute
  have derivativeSealUnary : UnaryHistory derivativeSeal :=
    unary_cont_closed derivativeReadUnary qUnary derivativeSealRoute
  have integralSealUnary : UnaryHistory integralSeal :=
    unary_cont_closed integralReadUnary qUnary integralSealRoute
  have derivativeSource :
      (fun row : BHist =>
        (hsame row derivativeSeal ∨ hsame row integralSeal) ∧ UnaryHistory row)
          derivativeSeal := by
    exact ⟨Or.inl (hsame_refl derivativeSeal), derivativeSealUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row derivativeSeal ∨ hsame row integralSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row I ∨ hsame row Q ∨ hsame row derivativeSeal ∨
              hsame row integralSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
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
          | inl sameDerivative =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameDerivative)
          | inr sameIntegral =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) sameIntegral)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameDerivative =>
          exact Or.inr (Or.inr (Or.inr (Or.inl sameDerivative)))
      | inr sameIntegral =>
          exact Or.inr (Or.inr (Or.inr (Or.inr sameIntegral)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, derivativeReadUnary, integralReadUnary, derivativeSealUnary,
      integralSealUnary⟩

end BEDC.Derived.CalculusUp
