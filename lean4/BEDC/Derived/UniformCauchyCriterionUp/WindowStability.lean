import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_window_stability [AskSetup] [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name index' windows'
      modulus' tolerance' tail' sealRow' transports' routes' provenance' name' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      hsame index index' →
        hsame windows windows' →
          hsame modulus modulus' →
            hsame tolerance tolerance' →
              hsame tail tail' →
                hsame sealRow sealRow' →
                  hsame transports transports' →
                    hsame routes routes' →
                      hsame provenance provenance' →
                        hsame name name' →
                          Cont index' windows' modulus' →
                            Cont modulus' tolerance' tail' →
                              Cont tail' sealRow' transports' →
                                Cont transports' routes' provenance' →
                                  PkgSig bundle name' pkg →
                                    UniformCauchyCriterionPacket index' windows' modulus'
                                          tolerance' tail' sealRow' transports' routes'
                                          provenance' name' bundle pkg ∧
                                      UnaryHistory index' ∧
                                        UnaryHistory windows' ∧
                                          UnaryHistory modulus' ∧
                                            UnaryHistory tolerance' ∧
                                              UnaryHistory tail' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet sameIndex sameWindows sameModulus sameTolerance sameTail sameSealRow
    sameTransports sameRoutes sameProvenance sameName indexWindowsModulus'
    modulusToleranceTail' tailSealRowTransports' transportsRoutesProvenance' namePkg'
  obtain ⟨indexUnary, windowsUnary, modulusUnary, toleranceUnary, tailUnary, sealRowUnary,
    transportsUnary, routesUnary, provenanceUnary, nameUnary, _indexWindowsModulus,
    _modulusToleranceTail, _tailSealRowTransports, _transportsRoutesProvenance, _namePkg⟩ :=
    packet
  have indexUnary' : UnaryHistory index' := unary_transport indexUnary sameIndex
  have windowsUnary' : UnaryHistory windows' := unary_transport windowsUnary sameWindows
  have modulusUnary' : UnaryHistory modulus' := unary_transport modulusUnary sameModulus
  have toleranceUnary' : UnaryHistory tolerance' :=
    unary_transport toleranceUnary sameTolerance
  have tailUnary' : UnaryHistory tail' := unary_transport tailUnary sameTail
  have sealRowUnary' : UnaryHistory sealRow' := unary_transport sealRowUnary sameSealRow
  have transportsUnary' : UnaryHistory transports' :=
    unary_transport transportsUnary sameTransports
  have routesUnary' : UnaryHistory routes' := unary_transport routesUnary sameRoutes
  have provenanceUnary' : UnaryHistory provenance' :=
    unary_transport provenanceUnary sameProvenance
  have nameUnary' : UnaryHistory name' := unary_transport nameUnary sameName
  exact
    ⟨⟨indexUnary', windowsUnary', modulusUnary', toleranceUnary', tailUnary',
        sealRowUnary', transportsUnary', routesUnary', provenanceUnary', nameUnary',
        indexWindowsModulus', modulusToleranceTail', tailSealRowTransports',
        transportsRoutesProvenance', namePkg'⟩,
      indexUnary', windowsUnary', modulusUnary', toleranceUnary', tailUnary'⟩

end BEDC.Derived.UniformCauchyCriterionUp
