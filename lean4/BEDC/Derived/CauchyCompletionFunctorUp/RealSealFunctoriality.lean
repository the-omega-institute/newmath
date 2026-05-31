import BEDC.Derived.CauchyCompletionFunctorUp

namespace BEDC.Derived.CauchyCompletionFunctorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyCompletionFunctorPacket_real_seal_functoriality [AskSetup] [PackageSetup]
    {metric regular sealRow monadRow universal classifier transport nameCert endpoint metric'
      regular' sealRow' monadRow' universal' classifier' transport' nameCert' endpoint'
      publicRead publicRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionFunctorPacket metric regular sealRow monadRow universal classifier transport
        nameCert endpoint bundle pkg ->
      CauchyCompletionFunctorPacket metric' regular' sealRow' monadRow' universal' classifier'
          transport' nameCert' endpoint' bundle pkg ->
        hsame metric metric' ->
          hsame regular regular' ->
            hsame sealRow sealRow' ->
              hsame monadRow monadRow' ->
                hsame universal universal' ->
                  Cont sealRow monadRow publicRead ->
                    Cont sealRow' monadRow' publicRead' ->
                      PkgSig bundle publicRead pkg ->
                        PkgSig bundle publicRead' pkg ->
                          hsame publicRead publicRead' ∧ hsame endpoint endpoint' ∧
                            UnaryHistory publicRead ∧ UnaryHistory publicRead' ∧
                              PkgSig bundle publicRead pkg ∧
                                PkgSig bundle publicRead' pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig ProbeBundle hsame UnaryHistory
  intro packet packet' _sameMetric _sameRegular sameSeal sameMonad sameUniversal
    sealMonadPublic sealMonadPublic' publicPkg publicPkg'
  obtain ⟨_metricUnary, _regularUnary, sealUnary, monadUnary, _universalUnary,
    _classifierUnary, _transportUnary, _nameCertUnary, _endpointUnary,
    _metricRegularSeal, monadUniversalEndpoint, _classifierTransportNameCert,
    _endpointPkg⟩ := packet
  obtain ⟨_metricUnary', _regularUnary', sealUnary', monadUnary', _universalUnary',
    _classifierUnary', _transportUnary', _nameCertUnary', _endpointUnary',
    _metricRegularSeal', monadUniversalEndpoint', _classifierTransportNameCert',
    _endpointPkg'⟩ := packet'
  have samePublic : hsame publicRead publicRead' :=
    cont_respects_hsame sameSeal sameMonad sealMonadPublic sealMonadPublic'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameMonad sameUniversal monadUniversalEndpoint monadUniversalEndpoint'
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary monadUnary sealMonadPublic
  have publicUnary' : UnaryHistory publicRead' :=
    unary_cont_closed sealUnary' monadUnary' sealMonadPublic'
  exact ⟨samePublic, sameEndpoint, publicUnary, publicUnary', publicPkg, publicPkg'⟩

end BEDC.Derived.CauchyCompletionFunctorUp
