import BEDC.Derived.UniformCauchyCriterionUp

namespace BEDC.Derived.UniformCauchyCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem UniformCauchyCriterionPacket_finite_window_selector_uniqueness [AskSetup]
    [PackageSetup]
    {index windows modulus tolerance tail sealRow transports routes provenance name index' windows'
      modulus' tolerance' tail' sealRow' transports' routes' provenance' name' windowRead
      windowRead' sealRead sealRead' realExtract realExtract' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformCauchyCriterionPacket index windows modulus tolerance tail sealRow transports routes
        provenance name bundle pkg →
      UniformCauchyCriterionPacket index' windows' modulus' tolerance' tail' sealRow'
          transports' routes' provenance' name' bundle pkg →
        hsame windows windows' →
          hsame tail tail' →
            hsame sealRow sealRow' →
              hsame windowRead windowRead' →
                hsame sealRead sealRead' →
                  Cont windows tail windowRead →
                    Cont windows' tail' windowRead' →
                      Cont tail sealRow sealRead →
                        Cont tail' sealRow' sealRead' →
                          Cont windowRead sealRead realExtract →
                            Cont windowRead' sealRead' realExtract' →
                              hsame realExtract realExtract' ∧ UnaryHistory realExtract ∧
                                UnaryHistory realExtract' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet packet' sameWindows sameTail sameSealRow sameWindowRead sameSealRead
    windowsTailRead windowsTailRead' tailSealRead tailSealRead' windowSealReal
    windowSealReal'
  obtain ⟨_indexUnary, windowsUnary, _modulusUnary, _toleranceUnary, tailUnary,
    sealRowUnary, _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary,
    _indexWindowsModulus, _modulusToleranceTail, _tailSealRowTransports,
    _transportsRoutesProvenance, _namePkg⟩ := packet
  obtain ⟨_indexUnary', windowsUnary', _modulusUnary', _toleranceUnary', tailUnary',
    sealRowUnary', _transportsUnary', _routesUnary', _provenanceUnary', _nameUnary',
    _indexWindowsModulus', _modulusToleranceTail', _tailSealRowTransports',
    _transportsRoutesProvenance', _namePkg'⟩ := packet'
  have _sameWindowReadFromRoute : hsame windowRead windowRead' :=
    cont_respects_hsame sameWindows sameTail windowsTailRead windowsTailRead'
  have _sameSealReadFromRoute : hsame sealRead sealRead' :=
    cont_respects_hsame sameTail sameSealRow tailSealRead tailSealRead'
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowsUnary tailUnary windowsTailRead
  have windowReadUnary' : UnaryHistory windowRead' :=
    unary_cont_closed windowsUnary' tailUnary' windowsTailRead'
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed tailUnary sealRowUnary tailSealRead
  have sealReadUnary' : UnaryHistory sealRead' :=
    unary_cont_closed tailUnary' sealRowUnary' tailSealRead'
  have realExtractUnary : UnaryHistory realExtract :=
    unary_cont_closed windowReadUnary sealReadUnary windowSealReal
  have realExtractUnary' : UnaryHistory realExtract' :=
    unary_cont_closed windowReadUnary' sealReadUnary' windowSealReal'
  have sameRealExtract : hsame realExtract realExtract' :=
    cont_respects_hsame sameWindowRead sameSealRead windowSealReal windowSealReal'
  exact ⟨sameRealExtract, realExtractUnary, realExtractUnary'⟩

end BEDC.Derived.UniformCauchyCriterionUp
