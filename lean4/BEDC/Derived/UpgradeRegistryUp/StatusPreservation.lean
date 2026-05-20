import BEDC.Derived.UpgradeRegistryUp.NameCertObligations

namespace BEDC.Derived.UpgradeRegistryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UpgradeRegistryStatusPreservation [AskSetup] [PackageSetup]
    {T S Nx F B A R H C P L statusRead blockerRead namedRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T -> UnaryHistory S -> UnaryHistory Nx -> UnaryHistory F ->
      UnaryHistory B -> UnaryHistory A -> UnaryHistory R -> UnaryHistory C ->
        UnaryHistory L -> Cont S Nx statusRead -> Cont F B blockerRead ->
          Cont C L namedRead -> Cont statusRead blockerRead exportRead ->
            PkgSig bundle namedRead pkg -> PkgSig bundle exportRead pkg ->
              UnaryHistory statusRead ∧ UnaryHistory blockerRead ∧
                UnaryHistory namedRead ∧ UnaryHistory exportRead ∧
                  Cont S Nx statusRead ∧ Cont F B blockerRead ∧
                    Cont statusRead blockerRead exportRead ∧
                      PkgSig bundle exportRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory
  intro _targetUnary statusUnary nextUnary fieldUnary blockerUnary _auditUnary
    _formalUnary continuationUnary localUnary statusCont blockerCont namedCont exportCont
    _namedPkg exportPkg
  have statusReadUnary : UnaryHistory statusRead :=
    unary_cont_closed statusUnary nextUnary statusCont
  have blockerReadUnary : UnaryHistory blockerRead :=
    unary_cont_closed fieldUnary blockerUnary blockerCont
  have namedReadUnary : UnaryHistory namedRead :=
    unary_cont_closed continuationUnary localUnary namedCont
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed statusReadUnary blockerReadUnary exportCont
  exact
    ⟨statusReadUnary, blockerReadUnary, namedReadUnary, exportReadUnary,
      statusCont, blockerCont, exportCont, exportPkg⟩

end BEDC.Derived.UpgradeRegistryUp
