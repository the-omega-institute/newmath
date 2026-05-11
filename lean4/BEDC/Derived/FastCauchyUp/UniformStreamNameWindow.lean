import BEDC.Derived.FastCauchyUp

namespace BEDC.Derived.FastCauchyUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FastCauchyFinitePacket_uniform_streamname_window_extraction [AskSetup] [PackageSetup]
    {stream modulus endpoint radius latePair transportWindow regWindow sealBoundary certRow
      precision selectedTransport selectedLatePair selectedRegWindow selectedCertRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FastCauchyFinitePacket stream modulus endpoint radius latePair transportWindow regWindow
        sealBoundary certRow bundle pkg ->
      UnaryHistory precision ->
        Cont stream precision selectedTransport ->
          Cont endpoint precision selectedLatePair ->
            Cont selectedLatePair selectedTransport selectedRegWindow ->
              Cont selectedRegWindow sealBoundary selectedCertRow ->
                PkgSig bundle selectedRegWindow pkg ->
                  FastCauchyFinitePacket stream precision endpoint precision selectedLatePair
                      selectedTransport selectedRegWindow sealBoundary selectedCertRow bundle pkg ∧
                    FastCauchyRegSeqRatWindow stream precision endpoint precision
                      selectedLatePair selectedTransport selectedRegWindow bundle pkg := by
  intro packet precisionUnary selectedTransportRow selectedLatePairRow selectedRegWindowRow
    selectedCertRowRow selectedRegWindowSig
  obtain ⟨streamUnary, _modulusUnary, endpointUnary, _radiusUnary, _latePairUnary,
    _transportUnary, _regUnary, sealUnary, _certUnary, _streamModulusRow,
    _endpointRadiusRow, _latePairTransportRow, _certRowRow, _packetSig⟩ := packet
  have selectedTransportUnary : UnaryHistory selectedTransport :=
    unary_cont_closed streamUnary precisionUnary selectedTransportRow
  have selectedLatePairUnary : UnaryHistory selectedLatePair :=
    unary_cont_closed endpointUnary precisionUnary selectedLatePairRow
  have selectedRegWindowUnary : UnaryHistory selectedRegWindow :=
    unary_cont_closed selectedLatePairUnary selectedTransportUnary selectedRegWindowRow
  have selectedCertRowUnary : UnaryHistory selectedCertRow :=
    unary_cont_closed selectedRegWindowUnary sealUnary selectedCertRowRow
  have extractedPacket :
      FastCauchyFinitePacket stream precision endpoint precision selectedLatePair
        selectedTransport selectedRegWindow sealBoundary selectedCertRow bundle pkg :=
    ⟨streamUnary, precisionUnary, endpointUnary, precisionUnary, selectedLatePairUnary,
      selectedTransportUnary, selectedRegWindowUnary, sealUnary, selectedCertRowUnary,
      selectedTransportRow, selectedLatePairRow, selectedRegWindowRow, selectedCertRowRow,
      selectedRegWindowSig⟩
  have extractedWindow :
      FastCauchyRegSeqRatWindow stream precision endpoint precision selectedLatePair
        selectedTransport selectedRegWindow bundle pkg :=
    ⟨streamUnary, precisionUnary, endpointUnary, precisionUnary, selectedLatePairUnary,
      selectedTransportUnary, selectedRegWindowUnary, selectedTransportRow, selectedLatePairRow,
      selectedRegWindowRow, selectedRegWindowSig⟩
  exact ⟨extractedPacket, extractedWindow⟩

end BEDC.Derived.FastCauchyUp
