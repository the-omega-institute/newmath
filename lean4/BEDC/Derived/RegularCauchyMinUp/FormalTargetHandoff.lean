import BEDC.Derived.RegularCauchyMinUp.CarrierAdmission
import BEDC.FKernel.Package

namespace BEDC.Derived.RegularCauchyMinUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyMinCarrier_formal_target_handoff [AskSetup] [PackageSetup]
    {A B W DA DB J S R E H C P N leftSelector rightSelector readbackRead sealRead
      publicRead formalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyMinCarrier A B W DA DB J S R E H C P N →
      Cont W DA leftSelector →
        Cont W DB rightSelector →
          Cont leftSelector J S →
            Cont S R readbackRead →
              Cont readbackRead E sealRead →
                Cont sealRead P publicRead →
                  Cont publicRead N formalRead →
                    PkgSig bundle P pkg →
                      PkgSig bundle N pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row formalRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                                hsame row DB ∨ hsame row J ∨ hsame row S ∨
                                  hsame row R ∨ hsame row E ∨ hsame row H ∨
                                    hsame row C ∨ hsame row P ∨ hsame row N ∨
                                      hsame row formalRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧
                                RegularCauchyMinCarrier A B W DA DB J S R E H C P N ∧
                                  Cont W DA leftSelector ∧ Cont W DB rightSelector ∧
                                    Cont leftSelector J S ∧ Cont S R readbackRead ∧
                                      Cont readbackRead E sealRead ∧
                                        Cont sealRead P publicRead ∧
                                          Cont publicRead N formalRead ∧
                                            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                            hsame ∧
                          UnaryHistory leftSelector ∧ UnaryHistory rightSelector ∧
                            UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                              UnaryHistory publicRead ∧ UnaryHistory formalRead := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier leftRoute rightRoute selectorRoute readbackRoute sealRoute publicRoute
    formalRoute pPkg nPkg
  have carrierWitness : RegularCauchyMinCarrier A B W DA DB J S R E H C P N :=
    carrier
  obtain ⟨_aUnary, _bUnary, wUnary, daUnary, dbUnary, jUnary, sUnary, rUnary,
    eUnary, _hUnary, _cUnary, pUnary, nUnary⟩ := carrier
  have leftUnary : UnaryHistory leftSelector :=
    unary_cont_closed wUnary daUnary leftRoute
  have rightUnary : UnaryHistory rightSelector :=
    unary_cont_closed wUnary dbUnary rightRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed sUnary rUnary readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary pUnary publicRoute
  have formalUnary : UnaryHistory formalRead :=
    unary_cont_closed publicUnary nUnary formalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row formalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
              hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row formalRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              RegularCauchyMinCarrier A B W DA DB J S R E H C P N ∧
                Cont W DA leftSelector ∧ Cont W DB rightSelector ∧
                  Cont leftSelector J S ∧ Cont S R readbackRead ∧
                    Cont readbackRead E sealRead ∧ Cont sealRead P publicRead ∧
                      Cont publicRead N formalRead ∧ PkgSig bundle P pkg ∧
                        PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro formalRead ⟨hsame_refl formalRead, formalUnary⟩
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
                                (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, carrierWitness, leftRoute, rightRoute, selectorRoute,
          readbackRoute, sealRoute, publicRoute, formalRoute, pPkg, nPkg⟩
  }
  exact
    ⟨cert, leftUnary, rightUnary, readbackUnary, sealUnary, publicUnary, formalUnary⟩

end BEDC.Derived.RegularCauchyMinUp
