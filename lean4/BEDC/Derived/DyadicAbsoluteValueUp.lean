import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.DyadicAbsoluteValueUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def DyadicAbsoluteValuePacket [AskSetup] [PackageSetup]
    (source sign mantissa endpoint tolerance transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory sign ∧ UnaryHistory mantissa ∧
    UnaryHistory endpoint ∧ UnaryHistory tolerance ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory name ∧
        Cont source sign mantissa ∧ Cont sign mantissa endpoint ∧
          Cont endpoint tolerance routes ∧ Cont routes provenance name ∧
            PkgSig bundle name pkg

theorem DyadicAbsoluteValuePacket_transport_stability [AskSetup] [PackageSetup]
    {source sign mantissa endpoint tolerance transport routes provenance name source' sign'
      mantissa' endpoint' tolerance' provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicAbsoluteValuePacket source sign mantissa endpoint tolerance transport routes provenance
        name bundle pkg ->
      hsame source source' ->
        hsame sign sign' ->
          hsame mantissa mantissa' ->
            hsame endpoint endpoint' ->
              hsame tolerance tolerance' ->
                hsame provenance provenance' ->
                  Cont source' sign' mantissa' ->
                    Cont sign' mantissa' endpoint' ->
                      Cont endpoint' tolerance' routes ->
                        Cont routes provenance' name' ->
                          PkgSig bundle name' pkg ->
                            DyadicAbsoluteValuePacket source' sign' mantissa' endpoint' tolerance'
                                transport routes provenance' name' bundle pkg /\
                              hsame name name' /\ UnaryHistory endpoint' /\
                                UnaryHistory tolerance' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro packet sameSource sameSign sameMantissa sameEndpoint sameTolerance sameProvenance
    sourceSignMantissa signMantissaEndpoint endpointToleranceRoutes routesProvenanceName namePkg
  obtain ⟨sourceUnary, signUnary, mantissaUnary, endpointUnary, toleranceUnary, transportUnary,
    routesUnary, provenanceUnary, _nameUnary, oldSourceSignMantissa, oldSignMantissaEndpoint,
    oldEndpointToleranceRoutes, oldRoutesProvenanceName, _oldNamePkg⟩ := packet
  have sourceUnary' : UnaryHistory source' :=
    unary_transport sourceUnary sameSource
  have signUnary' : UnaryHistory sign' :=
    unary_transport signUnary sameSign
  have mantissaUnary' : UnaryHistory mantissa' :=
    unary_transport mantissaUnary sameMantissa
  have endpointUnary' : UnaryHistory endpoint' :=
    unary_transport endpointUnary sameEndpoint
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport toleranceUnary sameTolerance
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have sameRoutes : hsame routes routes :=
    hsame_refl routes
  have sameName : hsame name name' :=
    cont_respects_hsame sameRoutes sameProvenance oldRoutesProvenanceName routesProvenanceName
  have transportedPacket :
      DyadicAbsoluteValuePacket source' sign' mantissa' endpoint' tolerance' transport routes
          provenance' name' bundle pkg := by
    exact
      ⟨sourceUnary', signUnary', mantissaUnary', endpointUnary', toleranceUnary',
        transportUnary, routesUnary, provenanceUnary',
        unary_transport _nameUnary sameName, sourceSignMantissa, signMantissaEndpoint,
        endpointToleranceRoutes, routesProvenanceName, namePkg⟩
  exact ⟨transportedPacket, sameName, endpointUnary', toleranceUnary'⟩

end BEDC.Derived.DyadicAbsoluteValueUp
