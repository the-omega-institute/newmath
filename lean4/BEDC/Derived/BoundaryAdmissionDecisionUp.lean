import BEDC.Derived.BoundaryAdmissionDecisionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BoundaryAdmissionDecisionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BoundaryAdmissionDecisionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {A C R B H _P N admissionRead routerRead boundaryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A ->
      UnaryHistory C ->
        UnaryHistory R ->
          UnaryHistory B ->
            UnaryHistory H ->
              UnaryHistory N ->
                Cont A C admissionRead ->
                  Cont admissionRead R routerRead ->
                    Cont routerRead B boundaryRead ->
                      PkgSig bundle N pkg ->
                        PkgSig bundle boundaryRead pkg ->
                          UnaryHistory admissionRead ∧ UnaryHistory routerRead ∧
                            UnaryHistory boundaryRead ∧ Cont A C admissionRead ∧
                              Cont admissionRead R routerRead ∧
                                Cont routerRead B boundaryRead ∧ PkgSig bundle N pkg ∧
                                  PkgSig bundle boundaryRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro aUnary cUnary rUnary bUnary _hUnary _nUnary admissionRoute routerRoute
    boundaryRoute namePkg boundaryPkg
  have admissionUnary : UnaryHistory admissionRead :=
    unary_cont_closed aUnary cUnary admissionRoute
  have routerUnary : UnaryHistory routerRead :=
    unary_cont_closed admissionUnary rUnary routerRoute
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed routerUnary bUnary boundaryRoute
  exact
    ⟨admissionUnary, routerUnary, boundaryUnary, admissionRoute, routerRoute, boundaryRoute,
      namePkg, boundaryPkg⟩

end BEDC.Derived.BoundaryAdmissionDecisionUp
