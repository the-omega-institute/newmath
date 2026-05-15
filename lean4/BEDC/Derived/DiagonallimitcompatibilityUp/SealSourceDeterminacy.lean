import BEDC.Derived.DiagonallimitcompatibilityUp

namespace BEDC.Derived.DiagonallimitcompatibilityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

theorem DiagonalLimitCompatibility_seal_source_determinacy [AskSetup] [PackageSetup]
    {diagonal triangle sealRow dyadic windows readback realSeal transport route provenance cert
      diagonal' triangle' sealRow' dyadic' windows' readback' realSeal' transport' route'
      provenance' cert' sealSource sealSource' sealRead sealRead' endpoint endpoint' consumer
      consumer' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DiagonalLimitCompatibilityCarrier diagonal triangle sealRow dyadic windows readback realSeal
        transport route provenance cert bundle pkg →
      DiagonalLimitCompatibilityCarrier diagonal' triangle' sealRow' dyadic' windows' readback'
        realSeal' transport' route' provenance' cert' bundle pkg →
        hsame diagonal diagonal' →
          hsame triangle triangle' →
            hsame dyadic dyadic' →
              hsame readback readback' →
                hsame realSeal realSeal' →
                  Cont diagonal triangle sealSource →
                    Cont diagonal' triangle' sealSource' →
                      Cont sealSource dyadic sealRead →
                        Cont sealSource' dyadic' sealRead' →
                          Cont readback realSeal endpoint →
                            Cont readback' realSeal' endpoint' →
                              Cont sealRead endpoint consumer →
                                Cont sealRead' endpoint' consumer' →
                                  hsame sealSource sealSource' ∧ hsame sealRead sealRead' ∧
                                    hsame endpoint endpoint' ∧ hsame consumer consumer' := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg
  intro carrier carrier' sameDiagonal sameTriangle sameDyadic sameReadback sameRealSeal
    diagonalTriangleSource diagonalTriangleSource' sourceDyadicRead sourceDyadicRead'
    readbackEndpoint readbackEndpoint' sealReadEndpoint sealReadEndpoint'
  have sameSealSource : hsame sealSource sealSource' :=
    cont_respects_hsame sameDiagonal sameTriangle diagonalTriangleSource
      diagonalTriangleSource'
  have sameSealRead : hsame sealRead sealRead' :=
    cont_respects_hsame sameSealSource sameDyadic sourceDyadicRead sourceDyadicRead'
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameReadback sameRealSeal readbackEndpoint readbackEndpoint'
  have sameConsumer : hsame consumer consumer' :=
    cont_respects_hsame sameSealRead sameEndpoint sealReadEndpoint sealReadEndpoint'
  exact ⟨sameSealSource, sameSealRead, sameEndpoint, sameConsumer⟩

end BEDC.Derived.DiagonallimitcompatibilityUp
