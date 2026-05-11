import BEDC.Derived.FastCauchyUp

namespace BEDC.Derived.FastCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
theorem FastCauchyFinitePacket_dyadicprecision_window_cofinality [AskSetup] [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow
      precision selectedThreshold selectedEndpoint selectedLatePair selectedWindow
      selectedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      UnaryHistory precision ->
        Cont modulus precision selectedThreshold ->
          Cont endpoint precision selectedEndpoint ->
            Cont latePair precision selectedLatePair ->
              Cont selectedThreshold selectedEndpoint selectedWindow ->
                Cont selectedLatePair selectedWindow selectedRead ->
                  PkgSig bundle selectedRead pkg ->
                    UnaryHistory selectedThreshold ∧ UnaryHistory selectedEndpoint ∧
                      UnaryHistory selectedLatePair ∧ UnaryHistory selectedWindow ∧
                        UnaryHistory selectedRead ∧ Cont modulus precision selectedThreshold ∧
                          Cont endpoint precision selectedEndpoint ∧
                            Cont latePair precision selectedLatePair ∧
                              Cont selectedThreshold selectedEndpoint selectedWindow ∧
                                Cont selectedLatePair selectedWindow selectedRead ∧
                                  PkgSig bundle selectedRead pkg := by
  intro packet precisionUnary thresholdRow endpointRow latePairRow windowRow readRow pkgRow
  obtain ⟨_streamUnary, modulusUnary, endpointUnary, _radiusUnary, latePairUnary,
    _transportUnary, _regUnary, _sealUnary, _certUnary, _streamModulusRoute,
    _endpointRadiusRoute, _latePairTransportRoute, _certRoute, _packetPkg⟩ := packet
  have thresholdUnary : UnaryHistory selectedThreshold :=
    unary_cont_closed modulusUnary precisionUnary thresholdRow
  have endpointSelectedUnary : UnaryHistory selectedEndpoint :=
    unary_cont_closed endpointUnary precisionUnary endpointRow
  have latePairSelectedUnary : UnaryHistory selectedLatePair :=
    unary_cont_closed latePairUnary precisionUnary latePairRow
  have windowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed thresholdUnary endpointSelectedUnary windowRow
  have readUnary : UnaryHistory selectedRead :=
    unary_cont_closed latePairSelectedUnary windowUnary readRow
  exact
    ⟨thresholdUnary, endpointSelectedUnary, latePairSelectedUnary, windowUnary, readUnary,
      thresholdRow, endpointRow, latePairRow, windowRow, readRow, pkgRow⟩

theorem FastCauchyFinitePacket_explicit_rate_seal_window_exhaustion [AskSetup]
    [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow
      precision selectedThreshold selectedEndpoint selectedLatePair selectedWindow selectedRead
      realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      UnaryHistory precision ->
        Cont modulus precision selectedThreshold ->
          Cont endpoint precision selectedEndpoint ->
            Cont latePair precision selectedLatePair ->
              Cont selectedThreshold selectedEndpoint selectedWindow ->
                Cont selectedLatePair selectedWindow selectedRead ->
                  Cont selectedRead sealBoundary realSeal ->
                    PkgSig bundle realSeal pkg ->
                      UnaryHistory selectedThreshold ∧ UnaryHistory selectedEndpoint ∧
                        UnaryHistory selectedLatePair ∧ UnaryHistory selectedWindow ∧
                          UnaryHistory selectedRead ∧ UnaryHistory realSeal ∧
                            Cont selectedRead sealBoundary realSeal ∧
                              PkgSig bundle realSeal pkg := by
  intro packet precisionUnary thresholdRow endpointRow latePairRow windowRow readRow sealRow pkgRow
  obtain ⟨_streamUnary, modulusUnary, endpointUnary, _radiusUnary, latePairUnary,
    _transportUnary, _regUnary, sealUnary, _certUnary, _streamModulusRoute,
    _endpointRadiusRoute, _latePairTransportRoute, _certRoute, _packetPkg⟩ := packet
  have thresholdUnary : UnaryHistory selectedThreshold :=
    unary_cont_closed modulusUnary precisionUnary thresholdRow
  have endpointSelectedUnary : UnaryHistory selectedEndpoint :=
    unary_cont_closed endpointUnary precisionUnary endpointRow
  have latePairSelectedUnary : UnaryHistory selectedLatePair :=
    unary_cont_closed latePairUnary precisionUnary latePairRow
  have windowUnary : UnaryHistory selectedWindow :=
    unary_cont_closed thresholdUnary endpointSelectedUnary windowRow
  have readUnary : UnaryHistory selectedRead :=
    unary_cont_closed latePairSelectedUnary windowUnary readRow
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed readUnary sealUnary sealRow
  exact ⟨thresholdUnary, endpointSelectedUnary, latePairSelectedUnary, windowUnary,
    readUnary, realSealUnary, sealRow, pkgRow⟩

end BEDC.Derived.FastCauchyUp
