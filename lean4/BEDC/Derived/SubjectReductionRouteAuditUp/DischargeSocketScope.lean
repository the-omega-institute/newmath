import BEDC.Derived.SubjectReductionRouteAuditUp.SocketHandoff

namespace BEDC.Derived.SubjectReductionRouteAuditUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SubjectReductionRouteAudit_discharge_socket_scope [AskSetup] [PackageSetup]
    {B E I U S H C P N exactRead invokeRead socketRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory B ->
      UnaryHistory E ->
        UnaryHistory I ->
          UnaryHistory U ->
            UnaryHistory S ->
              UnaryHistory H ->
                UnaryHistory C ->
                  UnaryHistory P ->
                    UnaryHistory N ->
                      Cont B E exactRead ->
                        Cont exactRead I invokeRead ->
                          Cont U S socketRead ->
                            Cont invokeRead socketRead namedRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  (∃ packet : BEDC.Derived.SubjectReductionRouteAuditUp,
                                      packet =
                                        BEDC.Derived.SubjectReductionRouteAuditUp.mk
                                          B E I U S H C P N) ∧
                                    UnaryHistory exactRead ∧ UnaryHistory invokeRead ∧
                                      UnaryHistory socketRead ∧ UnaryHistory namedRead ∧
                                        Cont U S socketRead ∧
                                          Cont invokeRead socketRead namedRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro unaryB unaryE unaryI unaryU unaryS _unaryH _unaryC _unaryP _unaryN exactRoute
    invokeRoute socketRoute namedRoute pkgP pkgN
  have exactUnary : UnaryHistory exactRead :=
    unary_cont_closed unaryB unaryE exactRoute
  have invokeUnary : UnaryHistory invokeRead :=
    unary_cont_closed exactUnary unaryI invokeRoute
  have socketUnary : UnaryHistory socketRead :=
    unary_cont_closed unaryU unaryS socketRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed invokeUnary socketUnary namedRoute
  exact
    ⟨Exists.intro
        (BEDC.Derived.SubjectReductionRouteAuditUp.mk B E I U S H C P N)
        rfl,
      exactUnary, invokeUnary, socketUnary, namedUnary, socketRoute, namedRoute, pkgP, pkgN⟩

end BEDC.Derived.SubjectReductionRouteAuditUp
