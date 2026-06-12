import BEDC.Derived.CauchyRateRealizationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyRateRealizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyRateRealizationNameCertObligations [AskSetup] [PackageSetup]
    {p r d s q m e H C P N rateRead windowRead toleranceRead readbackRead modulusRead
      sealRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory p →
      UnaryHistory r →
        UnaryHistory s →
          UnaryHistory d →
            UnaryHistory q →
              UnaryHistory m →
                UnaryHistory e →
                  UnaryHistory N →
                    Cont p r rateRead →
                      Cont rateRead s windowRead →
                        Cont windowRead d toleranceRead →
                          Cont toleranceRead q readbackRead →
                            Cont readbackRead m modulusRead →
                              Cont modulusRead e sealRead →
                                Cont sealRead N localRead →
                                  PkgSig bundle localRead pkg →
                                    SemanticNameCert
                                        (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row p ∨ hsame row r ∨ hsame row d ∨
                                            hsame row s ∨ hsame row q ∨ hsame row m ∨
                                              hsame row e ∨ hsame row H ∨ hsame row C ∨
                                                hsame row P ∨ hsame row N ∨
                                                  hsame row localRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont p r rateRead ∧
                                            Cont rateRead s windowRead ∧
                                              Cont windowRead d toleranceRead ∧
                                                Cont toleranceRead q readbackRead ∧
                                                  Cont readbackRead m modulusRead ∧
                                                    Cont modulusRead e sealRead ∧
                                                      Cont sealRead N localRead ∧
                                                        PkgSig bundle localRead pkg)
                                        hsame ∧
                                      UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro pUnary rUnary sUnary dUnary qUnary mUnary eUnary nUnary rateRoute windowRoute
    toleranceRoute readbackRoute modulusRoute sealRoute localRoute localPkg
  have rateUnary : UnaryHistory rateRead :=
    unary_cont_closed pUnary rUnary rateRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed rateUnary sUnary windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary dUnary toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary qUnary readbackRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed readbackUnary mUnary modulusRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusUnary eUnary sealRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed sealUnary nUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row p ∨ hsame row r ∨ hsame row d ∨ hsame row s ∨
              hsame row q ∨ hsame row m ∨ hsame row e ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont p r rateRead ∧ Cont rateRead s windowRead ∧
              Cont windowRead d toleranceRead ∧ Cont toleranceRead q readbackRead ∧
                Cont readbackRead m modulusRead ∧ Cont modulusRead e sealRead ∧
                  Cont sealRead N localRead ∧ PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left,
          unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, rateRoute, windowRoute, toleranceRoute, readbackRoute, modulusRoute,
          sealRoute, localRoute, localPkg⟩
  }
  exact ⟨cert, localUnary⟩

end BEDC.Derived.CauchyRateRealizationUp
