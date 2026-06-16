import BEDC.Derived.CauchySchwarzRealUp.Carrier

namespace BEDC.Derived.CauchySchwarzRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchySchwarzRealInnerproductBound [AskSetup] [PackageSetup]
    {V X Y I A B D Q S E H T P N boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySchwarzRealCarrier V X Y I A B D Q S E H T P N bundle pkg →
      Cont V X I →
        Cont I A D →
          Cont D Q S →
            Cont S E boundRead →
              PkgSig bundle boundRead pkg →
                UnaryHistory boundRead ∧ PkgSig bundle boundRead pkg ∧
                  hsame boundRead boundRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory hsame
  intro carrier vectorRoute scalarRoute dyadicRoute sealRoute boundPkg
  obtain ⟨vUnary, xUnary, _yUnary, _iUnary, aUnary, _bUnary, _dCarrierUnary,
    qUnary, _sCarrierUnary, eUnary, _hUnary, _tUnary, _pUnary, _nUnary,
    _provenancePkg⟩ := carrier
  have innerUnary : UnaryHistory I :=
    unary_cont_closed vUnary xUnary vectorRoute
  have dyadicUnary : UnaryHistory D :=
    unary_cont_closed innerUnary aUnary scalarRoute
  have streamUnary : UnaryHistory S :=
    unary_cont_closed dyadicUnary qUnary dyadicRoute
  have boundUnary : UnaryHistory boundRead :=
    unary_cont_closed streamUnary eUnary sealRoute
  exact ⟨boundUnary, boundPkg, hsame_refl boundRead⟩

end BEDC.Derived.CauchySchwarzRealUp
