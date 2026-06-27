import BEDC.Derived.CauchyDifferenceCriterionUp.BidirectionalExactness

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDifferenceCriterion_shift_invariance [AskSetup] [PackageSetup]
    {X Y D Z Q W T E H C P N X' Y' D' Z' Q' W' T' E' H' C' P' N'
      nullRead zeroRead sealRead nullRead' zeroRead' sealRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] ->
      cauchyDifferenceCriterionFields
          (CauchyDifferenceCriterionUp.mk X' Y' D' Z' Q' W' T' E' H' C' P' N') =
        [X', Y', D', Z', Q', W', T', E', H', C', P', N'] ->
        hsame X X' ->
          hsame Y Y' ->
            hsame D D' ->
              hsame Z Z' ->
                hsame Q Q' ->
                  hsame E E' ->
                    UnaryHistory D ->
                      UnaryHistory Z ->
                        UnaryHistory Q ->
                          UnaryHistory E ->
                            Cont D Z nullRead ->
                              Cont nullRead Q zeroRead ->
                                Cont zeroRead E sealRead ->
                                  Cont D' Z' nullRead' ->
                                    Cont nullRead' Q' zeroRead' ->
                                      Cont zeroRead' E' sealRead' ->
                                        PkgSig bundle P pkg ->
                                          PkgSig bundle N pkg ->
                                            hsame sealRead sealRead' ∧
                                              UnaryHistory nullRead ∧
                                                UnaryHistory zeroRead ∧
                                                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro fields fields' sameX sameY sameD sameZ sameQ sameE dUnary zUnary qUnary eUnary
    nullRoute zeroRoute sealRoute nullRoute' zeroRoute' sealRoute' pPkg nPkg
  have _acceptedFields :
      cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] := fields
  have _acceptedFields' :
      cauchyDifferenceCriterionFields
          (CauchyDifferenceCriterionUp.mk X' Y' D' Z' Q' W' T' E' H' C' P' N') =
        [X', Y', D', Z', Q', W', T', E', H', C', P', N'] := fields'
  have _sameSources : hsame X X' ∧ hsame Y Y' := ⟨sameX, sameY⟩
  have _pkgRows : PkgSig bundle P pkg ∧ PkgSig bundle N pkg := ⟨pPkg, nPkg⟩
  have nullUnary : UnaryHistory nullRead :=
    unary_cont_closed dUnary zUnary nullRoute
  have zeroUnary : UnaryHistory zeroRead :=
    unary_cont_closed nullUnary qUnary zeroRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed zeroUnary eUnary sealRoute
  have sameNull : hsame nullRead nullRead' :=
    cont_respects_hsame sameD sameZ nullRoute nullRoute'
  have sameZero : hsame zeroRead zeroRead' :=
    cont_respects_hsame sameNull sameQ zeroRoute zeroRoute'
  have sameSeal : hsame sealRead sealRead' :=
    cont_respects_hsame sameZero sameE sealRoute sealRoute'
  exact ⟨sameSeal, nullUnary, zeroUnary, sealUnary⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
