import BEDC.Derived.FiniteLebesgueNumberUp

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberTailRadiusTransportDeterminacy [AskSetup] [PackageSetup]
    {cover window radius mesh transport route provenance nameRow cover' window' radius' mesh'
      transport' route' provenance' nameRow' tailRead tailRead' consumerRead
      consumerRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport route provenance nameRow
        bundle pkg ->
      FiniteLebesgueNumberCarrier cover' window' radius' mesh' transport' route' provenance'
          nameRow' bundle pkg ->
        hsame radius radius' ->
          hsame mesh mesh' ->
            hsame nameRow nameRow' ->
              Cont radius mesh tailRead ->
                Cont radius' mesh' tailRead' ->
                  Cont tailRead nameRow consumerRead ->
                    Cont tailRead' nameRow' consumerRead' ->
                      PkgSig bundle consumerRead' pkg ->
                        hsame tailRead tailRead' ∧ hsame consumerRead consumerRead' ∧
                          UnaryHistory tailRead' ∧ UnaryHistory consumerRead' ∧
                            PkgSig bundle provenance pkg ∧
                              PkgSig bundle consumerRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont UnaryHistory
  intro carrier carrier' sameRadius sameMesh sameName tailCont tailCont' consumerCont
    consumerCont' consumerPkg'
  obtain ⟨_coverUnary, _windowUnary, _radiusUnary, _meshUnary, _transportUnary, _routeUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshRoute,
    _routeNameProvenance, provenancePkg⟩ := carrier
  obtain ⟨_coverUnary', _windowUnary', radiusUnary', meshUnary', _transportUnary',
    _routeUnary', _provenanceUnary', nameRowUnary', _coverWindowRadius', _radiusMeshRoute',
    _routeNameProvenance', _provenancePkg'⟩ := carrier'
  have sameTail : hsame tailRead tailRead' :=
    cont_respects_hsame sameRadius sameMesh tailCont tailCont'
  have sameConsumer : hsame consumerRead consumerRead' :=
    cont_respects_hsame sameTail sameName consumerCont consumerCont'
  have tailUnary' : UnaryHistory tailRead' :=
    unary_cont_closed radiusUnary' meshUnary' tailCont'
  have consumerUnary' : UnaryHistory consumerRead' :=
    unary_cont_closed tailUnary' nameRowUnary' consumerCont'
  exact
    ⟨sameTail, sameConsumer, tailUnary', consumerUnary', provenancePkg, consumerPkg'⟩

end BEDC.Derived.FiniteLebesgueNumberUp
