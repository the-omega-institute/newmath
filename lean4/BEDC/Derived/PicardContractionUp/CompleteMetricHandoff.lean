import BEDC.Derived.PicardContractionUp

namespace BEDC.Derived.PicardContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PicardContractionPacket_complete_metric_handoff [AskSetup] [PackageSetup]
    {banach contraction lipschitz iterates modulus endpoint transport routes provenance name
      cauchyRead sealRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PicardContractionPacket banach contraction lipschitz iterates modulus endpoint transport routes
        provenance name bundle pkg →
      Cont iterates modulus cauchyRead →
        Cont endpoint transport sealRead →
          Cont cauchyRead sealRead metricRead →
            PkgSig bundle cauchyRead pkg →
              PkgSig bundle sealRead pkg →
                PkgSig bundle metricRead pkg →
                  UnaryHistory banach ∧ UnaryHistory contraction ∧ UnaryHistory lipschitz ∧
                    UnaryHistory iterates ∧ UnaryHistory modulus ∧ UnaryHistory endpoint ∧
                      UnaryHistory cauchyRead ∧ UnaryHistory sealRead ∧
                        UnaryHistory metricRead ∧ Cont banach contraction lipschitz ∧
                          Cont iterates modulus endpoint ∧ Cont iterates modulus cauchyRead ∧
                            Cont endpoint transport sealRead ∧
                              Cont cauchyRead sealRead metricRead ∧ PkgSig bundle name pkg ∧
                                PkgSig bundle cauchyRead pkg ∧ PkgSig bundle sealRead pkg ∧
                                  PkgSig bundle metricRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro packet iteratesModulusCauchyRead endpointTransportSealRead cauchySealMetric
    cauchyReadPkg sealReadPkg metricReadPkg
  obtain ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
    endpointUnary, transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    banachContractionLipschitz, iteratesModulusEndpoint, _endpointTransportRoutes,
    _routesProvenanceName, namePkg⟩ := packet
  have cauchyReadUnary : UnaryHistory cauchyRead :=
    unary_cont_closed iteratesUnary modulusUnary iteratesModulusCauchyRead
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed endpointUnary transportUnary endpointTransportSealRead
  have metricReadUnary : UnaryHistory metricRead :=
    unary_cont_closed cauchyReadUnary sealReadUnary cauchySealMetric
  exact
    ⟨banachUnary, contractionUnary, lipschitzUnary, iteratesUnary, modulusUnary,
      endpointUnary, cauchyReadUnary, sealReadUnary, metricReadUnary,
      banachContractionLipschitz, iteratesModulusEndpoint, iteratesModulusCauchyRead,
      endpointTransportSealRead, cauchySealMetric, namePkg, cauchyReadPkg, sealReadPkg,
      metricReadPkg⟩

end BEDC.Derived.PicardContractionUp
