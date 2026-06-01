import BEDC.Derived.FareySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FareySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FareySequenceCarrier_stream_window_denominator_lock [AskSetup] [PackageSetup]
    {B A M L T S D Q W R G E H C P N windowRead readbackRead approxRead sealRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FareySequenceCarrier B A M L T S D Q W R G E H C P N bundle pkg ->
      Cont L T windowRead ->
        Cont windowRead W readbackRead ->
          Cont readbackRead R approxRead ->
            Cont approxRead G sealRead ->
              PkgSig bundle sealRead pkg ->
                UnaryHistory L ∧ UnaryHistory T ∧ UnaryHistory W ∧ UnaryHistory R ∧
                  UnaryHistory G ∧ UnaryHistory windowRead ∧ UnaryHistory readbackRead ∧
                    UnaryHistory approxRead ∧ UnaryHistory sealRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: FareySequenceCarrier BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier windowRoute readbackRoute approxRoute sealRoute sealPkg
  obtain ⟨_bUnary, _aUnary, _mUnary, lUnary, tUnary, _sUnary, _dUnary, _qUnary,
    wUnary, rUnary, gUnary, _eUnary, _hUnary, _cUnary, _pUnary, _nUnary,
    _aEmpty, _sEmpty, _mEmpty, _gEmpty, _eEmpty, provenancePkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed lUnary tUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary wUnary readbackRoute
  have approxUnary : UnaryHistory approxRead :=
    unary_cont_closed readbackUnary rUnary approxRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed approxUnary gUnary sealRoute
  exact
    ⟨lUnary, tUnary, wUnary, rUnary, gUnary, windowUnary, readbackUnary, approxUnary,
      sealUnary, provenancePkg, sealPkg⟩

end BEDC.Derived.FareySequenceUp
