import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

def CalculusLocalLinearizationCarrier [AskSetup] [PackageSetup]
    (E R D L J H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory E ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory L ∧
    UnaryHistory J ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont R D L ∧ Cont R D J ∧ Cont L H C ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CalculusLocalLinearizationCarrier_admission [AskSetup] [PackageSetup]
    {E R D L J H C P N derivativeRead integralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CalculusLocalLinearizationCarrier E R D L J H C P N bundle pkg →
      Cont L H derivativeRead →
        Cont J H integralRead →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row derivativeRead ∨ hsame row integralRead) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row E ∨ hsame row R ∨ hsame row D ∨ hsame row L ∨
                  hsame row J ∨ hsame row derivativeRead ∨ hsame row integralRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont L H derivativeRead ∧ Cont J H integralRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory derivativeRead ∧ UnaryHistory integralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier derivativeRoute integralRoute
  obtain ⟨eUnary, rUnary, dUnary, lUnary, jUnary, hUnary, _cUnary, _pUnary,
    _nUnary, _derivativeWindow, _integralWindow, _replayRoute, provenancePkg,
    namePkg⟩ := carrier
  have derivativeUnary : UnaryHistory derivativeRead :=
    unary_cont_closed lUnary hUnary derivativeRoute
  have integralUnary : UnaryHistory integralRead :=
    unary_cont_closed jUnary hUnary integralRoute
  have sourceDerivative :
      (hsame derivativeRead derivativeRead ∨ hsame derivativeRead integralRead) ∧
        UnaryHistory derivativeRead :=
    ⟨Or.inl (hsame_refl derivativeRead), derivativeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row derivativeRead ∨ hsame row integralRead) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row R ∨ hsame row D ∨ hsame row L ∨ hsame row J ∨
              hsame row derivativeRead ∨ hsame row integralRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L H derivativeRead ∧ Cont J H integralRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro derivativeRead sourceDerivative
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
        intro row row' sameRows source
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
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameDerivative)))))
      | inr sameIntegral =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sameIntegral)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, derivativeRoute, integralRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, derivativeUnary, integralUnary⟩

end BEDC.Derived.CalculusUp
