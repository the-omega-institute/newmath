import BEDC.Derived.CompactUniformContinuityUp

namespace BEDC.Derived.CompactUniformContinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CompactUniformContinuityPacket_classifier_transport [AskSetup] [PackageSetup]
    {source target graph tolerance precision net coverage modulusRows radiusRows fold transport
      route nameRow source' target' graph' tolerance' precision' net' coverage' modulusRows'
      radiusRows' fold' transport' route' nameRow' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CompactUniformContinuityPacket source target graph tolerance precision net coverage
        modulusRows radiusRows fold transport route nameRow bundle pkg →
      hsame source source' →
        hsame target target' →
          hsame graph graph' →
            hsame tolerance tolerance' →
              hsame precision precision' →
                hsame net net' →
                  hsame coverage coverage' →
                    hsame modulusRows modulusRows' →
                      hsame radiusRows radiusRows' →
                        hsame fold fold' →
                          hsame transport transport' →
                            hsame route route' →
                              hsame nameRow nameRow' →
                                CompactUniformContinuityPacket source' target' graph'
                                  tolerance' precision' net' coverage' modulusRows' radiusRows'
                                  fold' transport' route' nameRow' bundle pkg := by
  -- BEDC touchpoint anchor: BHist hsame Cont ProbeBundle PkgSig
  intro packet sameSource sameTarget sameGraph sameTolerance samePrecision sameNet
    sameCoverage sameModulusRows sameRadiusRows sameFold sameTransport sameRoute sameNameRow
  cases sameSource
  cases sameTarget
  cases sameGraph
  cases sameTolerance
  cases samePrecision
  cases sameNet
  cases sameCoverage
  cases sameModulusRows
  cases sameRadiusRows
  cases sameFold
  cases sameTransport
  cases sameRoute
  cases sameNameRow
  exact packet

end BEDC.Derived.CompactUniformContinuityUp
