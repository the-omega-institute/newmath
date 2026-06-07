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

theorem CalculusRootLimitDerivativeIntegralTriad [AskSetup] [PackageSetup]
    {C D I L Q Y R H T P N derivativeRead integralRead limitRead toleranceRead realRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory C →
      UnaryHistory D →
        UnaryHistory I →
          UnaryHistory L →
            UnaryHistory Q →
              UnaryHistory Y →
                UnaryHistory R →
                  Cont C D derivativeRead →
                    Cont C I integralRead →
                      Cont C L limitRead →
                        Cont Q Y toleranceRead →
                          Cont toleranceRead R realRead →
                            hsame H (append P N) →
                              PkgSig bundle P pkg →
                                PkgSig bundle N pkg →
                                  SemanticNameCert
                                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row C ∨ hsame row D ∨ hsame row I ∨
                                          hsame row L ∨ hsame row Q ∨ hsame row Y ∨
                                            hsame row R ∨ hsame row realRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧
                                          Cont C D derivativeRead ∧
                                            Cont C I integralRead ∧ Cont C L limitRead ∧
                                              Cont Q Y toleranceRead ∧
                                                Cont toleranceRead R realRead ∧
                                                  hsame H (append P N))
                                      hsame ∧
                                    UnaryHistory derivativeRead ∧ UnaryHistory integralRead ∧
                                      UnaryHistory limitRead ∧ UnaryHistory toleranceRead ∧
                                        UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert Pkg
  intro hC hD hI hL hQ hY hR derivativeRoute integralRoute limitRoute toleranceRoute
    realRoute structuralSame _pkgP _pkgN
  have hDerivative : UnaryHistory derivativeRead := unary_cont_closed hC hD derivativeRoute
  have hIntegral : UnaryHistory integralRead := unary_cont_closed hC hI integralRoute
  have hLimit : UnaryHistory limitRead := unary_cont_closed hC hL limitRoute
  have hTolerance : UnaryHistory toleranceRead := unary_cont_closed hQ hY toleranceRoute
  have hReal : UnaryHistory realRead := unary_cont_closed hTolerance hR realRoute
  have sourceReal : hsame realRead realRead ∧ UnaryHistory realRead :=
    ⟨hsame_refl realRead, hReal⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row C ∨ hsame row D ∨ hsame row I ∨ hsame row L ∨ hsame row Q ∨
              hsame row Y ∨ hsame row R ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C D derivativeRead ∧ Cont C I integralRead ∧
              Cont C L limitRead ∧ Cont Q Y toleranceRead ∧
                Cont toleranceRead R realRead ∧ hsame H (append P N))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead sourceReal
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, derivativeRoute, integralRoute, limitRoute, toleranceRoute, realRoute,
          structuralSame⟩
  }
  exact ⟨cert, hDerivative, hIntegral, hLimit, hTolerance, hReal⟩

end BEDC.Derived.CalculusUp
