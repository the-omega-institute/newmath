import BEDC.Derived.ZnormalUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_sibling_route_separation [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name siblingRead
      normalwordRoute hostTail : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont normal continuation siblingRead →
        Cont siblingRead routes normalwordRoute →
          PkgSig bundle normalwordRoute pkg →
            hsame siblingRead (append normal continuation) ∧ UnaryHistory normal ∧
              UnaryHistory continuation ∧ UnaryHistory siblingRead ∧ UnaryHistory routes ∧
                UnaryHistory normalwordRoute ∧ Cont typed fuel terminal ∧
                  Cont terminal normal continuation ∧ Cont continuation transports routes ∧
                    Cont normal continuation siblingRead ∧
                      Cont siblingRead routes normalwordRoute ∧ PkgSig bundle name pkg ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle normalwordRoute pkg ∧
                          (Cont siblingRead (BHist.e0 hostTail) normal → False) ∧
                            (Cont siblingRead (BHist.e1 hostTail) normal → False) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame PkgSig UnaryHistory
  intro packet normalContinuationSibling siblingRoutesNormalword normalwordRoutePkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, normalUnary, continuationUnary,
    _transportsUnary, routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have siblingSame : hsame siblingRead (append normal continuation) :=
    normalContinuationSibling
  have siblingUnary : UnaryHistory siblingRead :=
    unary_cont_closed normalUnary continuationUnary normalContinuationSibling
  have normalwordRouteUnary : UnaryHistory normalwordRoute :=
    unary_cont_closed siblingUnary routesUnary siblingRoutesNormalword
  have e0Refusal : Cont siblingRead (BHist.e0 hostTail) normal → False :=
    fun back =>
      cont_mutual_extension_right_tail_absurd.left normalContinuationSibling back
  have e1Refusal : Cont siblingRead (BHist.e1 hostTail) normal → False :=
    fun back =>
      cont_mutual_extension_right_tail_absurd.right normalContinuationSibling back
  exact
    ⟨siblingSame, normalUnary, continuationUnary, siblingUnary, routesUnary,
      normalwordRouteUnary, typedFuelTerminal, terminalNormalContinuation,
      continuationTransportsRoutes, normalContinuationSibling, siblingRoutesNormalword, namePkg,
      provenancePkg, normalwordRoutePkg, e0Refusal, e1Refusal⟩

end BEDC.Derived.ZnormalUp
