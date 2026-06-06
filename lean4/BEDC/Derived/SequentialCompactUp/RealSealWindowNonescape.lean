import BEDC.Derived.SequentialCompactUp.ObligationReadiness

namespace BEDC.Derived.SequentialCompactUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SequentialCompactRealSealWindowNonescape [AskSetup] [PackageSetup]
    {K B S W R E H C P N baireRead windowRead regularRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SequentialCompactCarrier K B S W R E H C P N bundle pkg ->
      Cont B S baireRead ->
        Cont baireRead W windowRead ->
          Cont windowRead R regularRead ->
            Cont regularRead E sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory B ∧ UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory R ∧
                  UnaryHistory E ∧ UnaryHistory baireRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory regularRead ∧ UnaryHistory sealRead ∧ Cont B S baireRead ∧
                      Cont baireRead W windowRead ∧ Cont windowRead R regularRead ∧
                        Cont regularRead E sealRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: SequentialCompactCarrier BHist ProbeBundle PkgSig Cont UnaryHistory
  intro carrier baireRoute windowRoute regularRoute sealRoute sealPkg
  obtain ⟨_kUnary, bUnary, sUnary, wUnary, rUnary, eUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _compactBaireStream, _streamWindowRegular, _regularSealTransport,
    _transportReplayProvenance, provenancePkg⟩ := carrier
  have baireUnary : UnaryHistory baireRead :=
    unary_cont_closed bUnary sUnary baireRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed baireUnary wUnary windowRoute
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed windowUnary rUnary regularRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed regularReadUnary eUnary sealRoute
  exact
    ⟨bUnary, sUnary, wUnary, rUnary, eUnary, baireUnary, windowUnary, regularReadUnary,
      sealUnary, baireRoute, windowRoute, regularRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.SequentialCompactUp
