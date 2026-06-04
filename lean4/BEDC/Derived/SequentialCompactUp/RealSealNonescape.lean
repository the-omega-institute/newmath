import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactCarrier_real_seal_nonescape [AskSetup] [PackageSetup]
    {K B S W R E H C P N selectedRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont S W selectedRead ->
        Cont selectedRead R regularRead ->
          Cont regularRead E sealRead ->
            PkgSig bundle sealRead pkg ->
              UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory R ∧ UnaryHistory E ∧
                UnaryHistory selectedRead ∧ UnaryHistory regularRead ∧
                  UnaryHistory sealRead ∧ Cont S W selectedRead ∧
                    Cont selectedRead R regularRead ∧ Cont regularRead E sealRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier selectedRoute regularRoute sealRoute sealPkg
  obtain ⟨_kUnary, _bUnary, sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have selectedUnary : UnaryHistory selectedRead :=
    unary_cont_closed sUnary wUnary selectedRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed selectedUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary eUnary sealRoute
  exact
    ⟨sUnary, wUnary, rUnary, eUnary, selectedUnary, regularReadUnary, sealUnary,
      selectedRoute, regularRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.SequentialCompactUp
