import BEDC.Derived.ModelPredictiveControlUp

namespace BEDC.Derived.ModelPredictiveControlUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def ModelPredictiveControlBHistCarrier [AskSetup] [PackageSetup]
    (X U N A Q W J T O F H R P C rolloutRead costRead terminalRead firstControlRead :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory U ∧ UnaryHistory N ∧ UnaryHistory A ∧
    UnaryHistory Q ∧ UnaryHistory W ∧ UnaryHistory J ∧ UnaryHistory T ∧
      UnaryHistory O ∧ UnaryHistory F ∧ UnaryHistory H ∧ UnaryHistory R ∧
        UnaryHistory P ∧ UnaryHistory C ∧ Cont X A rolloutRead ∧
          Cont rolloutRead J costRead ∧ Cont costRead T terminalRead ∧
            Cont O F firstControlRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle C pkg

theorem ModelPredictiveControlBHistCarrier_first_control_route [AskSetup] [PackageSetup]
    {X U N A Q W J T O F H R P C rolloutRead costRead terminalRead firstControlRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ModelPredictiveControlBHistCarrier X U N A Q W J T O F H R P C rolloutRead
        costRead terminalRead firstControlRead bundle pkg ->
      UnaryHistory rolloutRead ∧ UnaryHistory costRead ∧ UnaryHistory terminalRead ∧
        UnaryHistory firstControlRead ∧ Cont X A rolloutRead ∧
          Cont rolloutRead J costRead ∧ Cont costRead T terminalRead ∧
            Cont O F firstControlRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle C pkg := by
  -- BEDC touchpoint anchor: ModelPredictiveControlBHistCarrier BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier
  obtain ⟨unaryX, _unaryU, _unaryN, unaryA, _unaryQ, _unaryW, unaryJ, unaryT,
    unaryO, unaryF, _unaryH, _unaryR, _unaryP, _unaryC, rolloutRoute, costRoute,
    terminalRoute, firstControlRoute, provenancePkg, localNamePkg⟩ := carrier
  have rolloutUnary : UnaryHistory rolloutRead :=
    unary_cont_closed unaryX unaryA rolloutRoute
  have costUnary : UnaryHistory costRead :=
    unary_cont_closed rolloutUnary unaryJ costRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed costUnary unaryT terminalRoute
  have firstControlUnary : UnaryHistory firstControlRead :=
    unary_cont_closed unaryO unaryF firstControlRoute
  exact
    ⟨rolloutUnary, costUnary, terminalUnary, firstControlUnary, rolloutRoute,
      costRoute, terminalRoute, firstControlRoute, provenancePkg, localNamePkg⟩

end BEDC.Derived.ModelPredictiveControlUp
