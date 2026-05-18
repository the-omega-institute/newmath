import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_window_refinement_exactness
    [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name windows'
      modulus' tolerance' tail' sealRow' transports' routes' provenance' name' refinedWindow
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      hsame windows windows' →
        hsame modulus modulus' →
          hsame tolerance tolerance' →
            hsame sealRow sealRow' →
              hsame routes routes' →
                hsame provenance provenance' →
                  hsame name name' →
                    Cont index windows refinedWindow →
                      Cont index windows' modulus' →
                        Cont modulus' tolerance' tail' →
                          Cont tail' sealRow' transports' →
                            Cont transports' routes' provenance' →
                              PkgSig bundle name' pkg →
                                Cont tail' sealRow' sealRead →
                                  PkgSig bundle sealRead pkg →
                                    UniformCauchyCriterionPacket index windows' modulus'
                                          tolerance' tail' sealRow' transports' routes'
                                          provenance' name' bundle pkg ∧
                                      hsame tail tail' ∧
                                        UnaryHistory refinedWindow ∧
                                          UnaryHistory sealRead ∧
                                            Cont index windows refinedWindow ∧
                                              Cont tail' sealRow' sealRead ∧
                                                PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packetIn sameWindows sameModulus sameTolerance sameSealRow sameRoutes sameProvenance
    sameName indexWindowsRefined indexWindowsModulus' modulusToleranceTail'
    tailSealRowTransports' transportsRoutesProvenance' namePkg' tailSealRead sealReadPkg
  obtain ⟨indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, _tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packetIn
  have modulusUnary' : UnaryHistory modulus' :=
    unary_transport _modulusUnary sameModulus
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport _toleranceUnary sameTolerance
  have tailSame : hsame tail tail' :=
    cont_respects_hsame sameModulus sameTolerance _modulusToleranceTail modulusToleranceTail'
  have tailUnary' : UnaryHistory tail' :=
    unary_cont_closed modulusUnary' toleranceUnary' modulusToleranceTail'
  have windowsUnary' : UnaryHistory windows' :=
    unary_transport windowsUnary sameWindows
  have sealRowUnary' : UnaryHistory sealRow' :=
    unary_transport sealRowUnary sameSealRow
  have transportsUnary' : UnaryHistory transports' :=
    unary_cont_closed tailUnary' sealRowUnary' tailSealRowTransports'
  have routesUnary' : UnaryHistory routes' :=
    unary_transport _routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport _provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' :=
    unary_transport _nameUnary sameName
  have packetOut :
      UniformCauchyCriterionPacket index windows' modulus' tolerance' tail' sealRow'
        transports' routes' provenance' name' bundle pkg :=
    ⟨indexUnary, windowsUnary', modulusUnary', toleranceUnary', tailUnary', sealRowUnary',
      transportsUnary', routesUnary', provenanceUnary', nameUnary', indexWindowsModulus',
      modulusToleranceTail', tailSealRowTransports', transportsRoutesProvenance', namePkg'⟩
  have refinedWindowUnary : UnaryHistory refinedWindow :=
    unary_cont_closed indexUnary windowsUnary indexWindowsRefined
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary' sealRowUnary' tailSealRead
  exact
    ⟨packetOut, tailSame, refinedWindowUnary, sealReadUnary, indexWindowsRefined, tailSealRead,
      sealReadPkg⟩

end BEDC.Derived.UniformCauchyCriterionUp
