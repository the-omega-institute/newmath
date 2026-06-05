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

theorem CalculusRiemannDerivativeSeparation [AskSetup] [PackageSetup]
    {E R D L J H C P N derivativeRead integralRead derivativeSeal integralSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory R →
      UnaryHistory D →
        UnaryHistory L →
          UnaryHistory J →
            UnaryHistory E →
              Cont R D derivativeRead →
                Cont R D integralRead →
                  Cont derivativeRead L derivativeSeal →
                    Cont integralRead J integralSeal →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row derivativeSeal ∨ hsame row integralSeal) ∧
                                  UnaryHistory row)
                              (fun row : BHist =>
                                hsame row L ∨ hsame row J ∨ hsame row derivativeSeal ∨
                                  hsame row integralSeal)
                              (fun row : BHist =>
                                UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle N pkg)
                              hsame ∧
                            UnaryHistory derivativeSeal ∧ UnaryHistory integralSeal := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro rUnary dUnary lUnary jUnary _eUnary derivativeRoute integralRoute derivativePublic
    integralPublic provenancePkg namePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed rUnary dUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed rUnary dUnary integralRoute
  have derivativeSealUnary : UnaryHistory derivativeSeal :=
    unary_cont_closed derivativeReadUnary lUnary derivativePublic
  have integralSealUnary : UnaryHistory integralSeal :=
    unary_cont_closed integralReadUnary jUnary integralPublic
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row derivativeSeal ∨ hsame row integralSeal) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row J ∨ hsame row derivativeSeal ∨
              hsame row integralSeal)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro derivativeSeal ⟨Or.inl (hsame_refl derivativeSeal), derivativeSealUnary⟩
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
          | inr integralSame =>
              exact Or.inr (hsame_trans (hsame_symm sameRows) integralSame)
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl derivativeSame =>
          exact Or.inr (Or.inr (Or.inl derivativeSame))
      | inr integralSame =>
          exact Or.inr (Or.inr (Or.inr integralSame))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, namePkg⟩
  }
  exact ⟨cert, derivativeSealUnary, integralSealUnary⟩

end BEDC.Derived.CalculusUp
