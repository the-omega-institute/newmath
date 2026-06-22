import BEDC.Derived.CauchySchwarzRealUp.Carrier

namespace BEDC.Derived.CauchySchwarzRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem CauchySchwarzRealInnerproductBound_namecert_consumer [AskSetup] [PackageSetup]
    {V X Y I A B D Q S E H T P N boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySchwarzRealCarrier V X Y I A B D Q S E H T P N bundle pkg →
      Cont V X I →
        PkgSig bundle I pkg →
          Cont I A D →
            Cont D Q S →
              Cont S E boundRead →
                PkgSig bundle boundRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row I ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row V ∨ hsame row X ∨ hsame row Y ∨ hsame row I ∨
                          hsame row A ∨ hsame row B ∨ hsame row D ∨ hsame row Q ∨
                            hsame row S ∨ hsame row E ∨ hsame row I)
                      (fun row : BHist => hsame row I ∧ PkgSig bundle I pkg)
                      hsame ∧
                    UnaryHistory boundRead ∧ PkgSig bundle boundRead pkg ∧
                      hsame boundRead boundRead ∧ Cont V X I ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle I pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert UnaryHistory
  intro carrier vectorRoute routePkg scalarRoute dyadicRoute sealRoute boundPkg
  have obligations :=
    CauchySchwarzRealCarrier_namecert_obligations carrier vectorRoute routePkg
  have bound :=
    CauchySchwarzRealInnerproductBound carrier vectorRoute scalarRoute dyadicRoute sealRoute
      boundPkg
  exact
    ⟨obligations.left, bound.left, bound.right.left, bound.right.right,
      obligations.right.right.left, obligations.right.right.right.left,
      obligations.right.right.right.right⟩

end BEDC.Derived.CauchySchwarzRealUp
