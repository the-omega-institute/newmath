import BEDC.Derived.RegularCauchyTailScheduleUp.TasteGate

namespace BEDC.Derived.RegularCauchyTailScheduleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailSchedule_window_readiness [AskSetup] [PackageSetup]
    {precision source window dyadic cofinal tail meet fusion sealRow transport route provenance
      name scheduleRead tailRead meetRead fusionRead sealedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailScheduleCarrier precision source window dyadic cofinal tail meet fusion
        sealRow transport route provenance name bundle pkg →
      Cont precision source scheduleRead →
        Cont scheduleRead window tailRead →
          Cont tailRead meet meetRead →
            Cont tailRead fusion fusionRead →
              Cont fusionRead sealRow sealedRead →
                UnaryHistory scheduleRead ∧ UnaryHistory tailRead ∧ UnaryHistory meetRead ∧
                  UnaryHistory fusionRead ∧ UnaryHistory sealedRead ∧
                    hsame tailRead (append scheduleRead window) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory ProbeBundle Pkg
  intro carrier scheduleRoute tailRoute meetRoute fusionRoute sealRoute
  obtain ⟨precisionUnary, sourceUnary, windowUnary, _dyadicUnary, _cofinalUnary,
    _tailUnary, meetUnary, fusionUnary, sealUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameUnary, _precisionSourceRoute, _routeWindowTail,
    _tailMeetFusion, _fusionSealTransport, _provenancePkg, _namePkg⟩ := carrier
  have scheduleUnary : UnaryHistory scheduleRead :=
    unary_cont_closed precisionUnary sourceUnary scheduleRoute
  have tailReadUnary : UnaryHistory tailRead :=
    unary_cont_closed scheduleUnary windowUnary tailRoute
  have meetReadUnary : UnaryHistory meetRead :=
    unary_cont_closed tailReadUnary meetUnary meetRoute
  have fusionReadUnary : UnaryHistory fusionRead :=
    unary_cont_closed tailReadUnary fusionUnary fusionRoute
  have sealedReadUnary : UnaryHistory sealedRead :=
    unary_cont_closed fusionReadUnary sealUnary sealRoute
  exact
    ⟨scheduleUnary, tailReadUnary, meetReadUnary, fusionReadUnary, sealedReadUnary,
      tailRoute⟩

end BEDC.Derived.RegularCauchyTailScheduleUp
