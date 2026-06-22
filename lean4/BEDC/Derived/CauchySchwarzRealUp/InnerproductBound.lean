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

theorem CauchySchwarzRealInnerproductBound_norm_handoff_consumer [AskSetup] [PackageSetup]
    {V X Y I A B D Q S E H T P N vectorRead scalarRead squareRead readbackRead
      sealRead normRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySchwarzRealCarrier V X Y I A B D Q S E H T P N bundle pkg →
      Cont V X vectorRead →
        Cont vectorRead I scalarRead →
          Cont scalarRead D squareRead →
            Cont squareRead Q readbackRead →
              Cont readbackRead E sealRead →
                Cont sealRead H normRead →
                  PkgSig bundle normRead pkg →
                    UnaryHistory normRead ∧ PkgSig bundle normRead pkg ∧
                      hsame normRead normRead ∧ Cont sealRead H normRead ∧
                        PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory hsame
  intro carrier vectorRoute scalarRoute squareRoute readbackRoute sealRoute normRoute normPkg
  have handoff :=
    CauchySchwarzRealCarrier_norm_bound_handoff carrier vectorRoute scalarRoute squareRoute
      readbackRoute sealRoute normRoute normPkg
  exact
    ⟨handoff.left, handoff.right.right.right, hsame_refl normRead, handoff.right.left,
      handoff.right.right.left⟩

end BEDC.Derived.CauchySchwarzRealUp
