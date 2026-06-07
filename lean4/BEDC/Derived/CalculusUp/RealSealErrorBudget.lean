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

theorem CalculusRealSealErrorBudget [AskSetup] [PackageSetup]
    {derivativeRow integralRow readbackRow toleranceRow realSeal transport replay provenance
      localName derivativeRead integralRead derivativeToleranceRead integralToleranceRead
      derivativeSealRead integralSealRead structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory derivativeRow ->
      UnaryHistory integralRow ->
        UnaryHistory readbackRow ->
          UnaryHistory toleranceRow ->
            UnaryHistory realSeal ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont derivativeRow readbackRow derivativeRead ->
                    Cont integralRow readbackRow integralRead ->
                      Cont derivativeRead toleranceRow derivativeToleranceRead ->
                        Cont integralRead toleranceRow integralToleranceRead ->
                          Cont derivativeToleranceRead realSeal derivativeSealRead ->
                            Cont integralToleranceRead realSeal integralSealRead ->
                              Cont transport replay structuralRead ->
                                PkgSig bundle provenance pkg ->
                                  PkgSig bundle localName pkg ->
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        (hsame row derivativeSealRead ∨
                                          hsame row integralSealRead) ∧
                                          UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row derivativeRow ∨ hsame row integralRow ∨
                                          hsame row readbackRow ∨ hsame row toleranceRow ∨
                                            hsame row realSeal ∨
                                              hsame row derivativeSealRead ∨
                                                hsame row integralSealRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont derivativeRow readbackRow derivativeRead ∧
                                            Cont integralRow readbackRow integralRead ∧
                                              Cont derivativeRead toleranceRow
                                                derivativeToleranceRead ∧
                                                Cont integralRead toleranceRow
                                                  integralToleranceRead ∧
                                                  Cont derivativeToleranceRead realSeal
                                                    derivativeSealRead ∧
                                                    Cont integralToleranceRead realSeal
                                                      integralSealRead ∧
                                                      PkgSig bundle provenance pkg ∧
                                                        PkgSig bundle localName pkg)
                                      hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro derivativeUnary integralUnary readbackUnary toleranceUnary realSealUnary _transportUnary
    _replayUnary derivativeRoute integralRoute derivativeToleranceRoute integralToleranceRoute
    derivativeSealRoute integralSealRoute _structuralRoute provenancePkg localNamePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed derivativeUnary readbackUnary derivativeRoute
  have integralReadUnary : UnaryHistory integralRead :=
    unary_cont_closed integralUnary readbackUnary integralRoute
  have derivativeToleranceUnary : UnaryHistory derivativeToleranceRead :=
    unary_cont_closed derivativeReadUnary toleranceUnary derivativeToleranceRoute
  have integralToleranceUnary : UnaryHistory integralToleranceRead :=
    unary_cont_closed integralReadUnary toleranceUnary integralToleranceRoute
  have derivativeSealUnary : UnaryHistory derivativeSealRead :=
    unary_cont_closed derivativeToleranceUnary realSealUnary derivativeSealRoute
  have sourceSeal :
      (fun row : BHist =>
        (hsame row derivativeSealRead ∨ hsame row integralSealRead) ∧
          UnaryHistory row) derivativeSealRead := by
    exact ⟨Or.inl (hsame_refl derivativeSealRead), derivativeSealUnary⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro derivativeSealRead sourceSeal
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
          exact Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inl derivativeSame)))))
      | inr integralSame =>
          exact Or.inr
            (Or.inr
              (Or.inr (Or.inr (Or.inr (Or.inr integralSame)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, derivativeRoute, integralRoute, derivativeToleranceRoute,
          integralToleranceRoute, derivativeSealRoute, integralSealRoute,
          provenancePkg, localNamePkg⟩
  }

end BEDC.Derived.CalculusUp
