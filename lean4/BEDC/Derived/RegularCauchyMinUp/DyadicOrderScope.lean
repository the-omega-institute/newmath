import BEDC.Derived.RegularCauchyMinUp.CarrierAdmission
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyMinCarrier_dyadic_order_scope [AskSetup] [PackageSetup]
    {A B W DA DB J S R E H C P N leftWindow rightWindow leftLedger rightLedger
      selectorRead readbackRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyMinCarrier A B W DA DB J S R E H C P N ->
      Cont A W leftWindow ->
        Cont B W rightWindow ->
          Cont leftWindow DA leftLedger ->
            Cont rightWindow DB rightLedger ->
              Cont J S selectorRead ->
                Cont selectorRead R readbackRead ->
                  Cont readbackRead E sealRead ->
                    PkgSig bundle P pkg ->
                      PkgSig bundle N pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row A ∨ hsame row B ∨ hsame row W ∨
                                hsame row DA ∨ hsame row DB ∨ hsame row J ∨
                                  hsame row S ∨ hsame row R ∨ hsame row E ∨
                                    hsame row H ∨ hsame row C ∨ hsame row P ∨
                                      hsame row N ∨ hsame row leftWindow ∨
                                        hsame row rightWindow ∨ hsame row leftLedger ∨
                                          hsame row rightLedger ∨ hsame row selectorRead ∨
                                            hsame row readbackRead ∨ hsame row sealRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont A W leftWindow ∧
                                Cont B W rightWindow ∧ Cont leftWindow DA leftLedger ∧
                                  Cont rightWindow DB rightLedger ∧ Cont J S selectorRead ∧
                                    Cont selectorRead R readbackRead ∧
                                      Cont readbackRead E sealRead ∧
                                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧ UnaryHistory leftWindow ∧ UnaryHistory rightWindow ∧
                          UnaryHistory leftLedger ∧ UnaryHistory rightLedger ∧
                            UnaryHistory selectorRead ∧ UnaryHistory readbackRead ∧
                              UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier leftWindowRoute rightWindowRoute leftLedgerRoute rightLedgerRoute
    selectorRoute readbackRoute sealRoute provenancePkg namePkg
  obtain ⟨aUnary, bUnary, wUnary, daUnary, dbUnary, jUnary, sUnary, rUnary, eUnary,
    _hUnary, _cUnary, _pUnary, _nUnary⟩ := carrier
  have leftWindowUnary : UnaryHistory leftWindow :=
    unary_cont_closed aUnary wUnary leftWindowRoute
  have rightWindowUnary : UnaryHistory rightWindow :=
    unary_cont_closed bUnary wUnary rightWindowRoute
  have leftLedgerUnary : UnaryHistory leftLedger :=
    unary_cont_closed leftWindowUnary daUnary leftLedgerRoute
  have rightLedgerUnary : UnaryHistory rightLedger :=
    unary_cont_closed rightWindowUnary dbUnary rightLedgerRoute
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed jUnary sUnary selectorRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed selectorUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
              hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row leftWindow ∨ hsame row rightWindow ∨
                    hsame row leftLedger ∨ hsame row rightLedger ∨
                      hsame row selectorRead ∨ hsame row readbackRead ∨
                        hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A W leftWindow ∧ Cont B W rightWindow ∧
              Cont leftWindow DA leftLedger ∧ Cont rightWindow DB rightLedger ∧
                Cont J S selectorRead ∧ Cont selectorRead R readbackRead ∧
                  Cont readbackRead E sealRead ∧ PkgSig bundle P pkg ∧
                    PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr source.left))))))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, leftWindowRoute, rightWindowRoute, leftLedgerRoute,
          rightLedgerRoute, selectorRoute, readbackRoute, sealRoute, provenancePkg, namePkg⟩
  }
  exact
    ⟨cert, leftWindowUnary, rightWindowUnary, leftLedgerUnary, rightLedgerUnary,
      selectorUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.RegularCauchyMinUp
