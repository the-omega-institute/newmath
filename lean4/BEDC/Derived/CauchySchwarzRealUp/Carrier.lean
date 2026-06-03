import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.CauchySchwarzRealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchySchwarzRealCarrier [AskSetup] [PackageSetup]
    (V X Y I A B D Q S E H T P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory V ∧ UnaryHistory X ∧ UnaryHistory Y ∧ UnaryHistory I ∧
    UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory D ∧ UnaryHistory Q ∧
      UnaryHistory S ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory T ∧
        UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem CauchySchwarzRealCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {V X Y I A B D Q S E H T P N routeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySchwarzRealCarrier V X Y I A B D Q S E H T P N bundle pkg →
      Cont V X routeRead →
        PkgSig bundle routeRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row V ∨ hsame row X ∨ hsame row Y ∨ hsame row I ∨
                  hsame row A ∨ hsame row B ∨ hsame row D ∨ hsame row Q ∨
                    hsame row S ∨ hsame row E ∨ hsame row routeRead)
              (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
              hsame ∧
            UnaryHistory routeRead ∧ Cont V X routeRead ∧ PkgSig bundle P pkg ∧
              PkgSig bundle routeRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame UnaryHistory
  intro carrier vectorRoute routePkg
  obtain ⟨vUnary, xUnary, _yUnary, _iUnary, _aUnary, _bUnary, _dUnary, _qUnary,
    _sUnary, _eUnary, _hUnary, _tUnary, _pUnary, _nUnary, provenancePkg⟩ := carrier
  have routeUnary : UnaryHistory routeRead :=
    unary_cont_closed vUnary xUnary vectorRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row X ∨ hsame row Y ∨ hsame row I ∨
              hsame row A ∨ hsame row B ∨ hsame row D ∨ hsame row Q ∨
                hsame row S ∨ hsame row E ∨ hsame row routeRead)
          (fun row : BHist => hsame row routeRead ∧ PkgSig bundle routeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routePkg⟩
  }
  exact ⟨cert, routeUnary, vectorRoute, provenancePkg, routePkg⟩

theorem CauchySchwarzRealCarrier_dyadic_square_handoff [AskSetup] [PackageSetup]
    {V X Y I A B D Q S E H T P N vectorRead scalarRead squareRead readbackRead
      sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchySchwarzRealCarrier V X Y I A B D Q S E H T P N bundle pkg →
      Cont V X vectorRead →
        Cont vectorRead I scalarRead →
          Cont scalarRead D squareRead →
            Cont squareRead Q readbackRead →
              Cont readbackRead E sealRead →
                PkgSig bundle sealRead pkg →
                  UnaryHistory V ∧ UnaryHistory X ∧ UnaryHistory I ∧ UnaryHistory D ∧
                    UnaryHistory Q ∧ UnaryHistory E ∧ UnaryHistory vectorRead ∧
                      UnaryHistory scalarRead ∧ UnaryHistory squareRead ∧
                        UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                          Cont V X vectorRead ∧ Cont vectorRead I scalarRead ∧
                            Cont scalarRead D squareRead ∧
                              Cont squareRead Q readbackRead ∧
                                Cont readbackRead E sealRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle sealRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg UnaryHistory PkgSig
  intro carrier vectorRoute scalarRoute squareRoute readbackRoute sealRoute sealPkg
  obtain ⟨vUnary, xUnary, _yUnary, iUnary, _aUnary, _bUnary, dUnary, qUnary,
    _sUnary, eUnary, _hUnary, _tUnary, _pUnary, _nUnary, provenancePkg⟩ := carrier
  have vectorUnary : UnaryHistory vectorRead :=
    unary_cont_closed vUnary xUnary vectorRoute
  have scalarUnary : UnaryHistory scalarRead :=
    unary_cont_closed vectorUnary iUnary scalarRoute
  have squareUnary : UnaryHistory squareRead :=
    unary_cont_closed scalarUnary dUnary squareRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed squareUnary qUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  exact
    ⟨vUnary, xUnary, iUnary, dUnary, qUnary, eUnary, vectorUnary, scalarUnary,
      squareUnary, readbackUnary, sealUnary, vectorRoute, scalarRoute, squareRoute,
      readbackRoute, sealRoute, provenancePkg, sealPkg⟩

end BEDC.Derived.CauchySchwarzRealUp
