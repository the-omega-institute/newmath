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

theorem RegularCauchyMinCarrier_kernel_scope_route [AskSetup] [PackageSetup]
    {A B W DA DB J S R E H C P N selectorRead orderRead sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyMinCarrier A B W DA DB J S R E H C P N →
      Cont W DA selectorRead →
        Cont selectorRead J orderRead →
          Cont orderRead E sealRead →
            Cont sealRead P publicRead →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
                        hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                          hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                            hsame row N ∨ hsame row selectorRead ∨
                              hsame row orderRead ∨ hsame row sealRead ∨
                                hsame row publicRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W DA selectorRead ∧
                        Cont selectorRead J orderRead ∧ Cont orderRead E sealRead ∧
                          Cont sealRead P publicRead ∧ PkgSig bundle publicRead pkg)
                    hsame ∧ UnaryHistory selectorRead ∧ UnaryHistory orderRead ∧
                      UnaryHistory sealRead ∧ UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: RegularCauchyMinUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier selectorRoute orderRoute sealRoute publicRoute publicPkg
  obtain ⟨_aUnary, _bUnary, wUnary, daUnary, _dbUnary, jUnary, _sUnary, _rUnary,
    eUnary, _hUnary, _cUnary, pUnary, _nUnary⟩ := carrier
  have selectorUnary : UnaryHistory selectorRead :=
    unary_cont_closed wUnary daUnary selectorRoute
  have orderUnary : UnaryHistory orderRead :=
    unary_cont_closed selectorUnary jUnary orderRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed orderUnary eUnary sealRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed sealUnary pUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row W ∨ hsame row DA ∨
              hsame row DB ∨ hsame row J ∨ hsame row S ∨ hsame row R ∨
                hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                  hsame row N ∨ hsame row selectorRead ∨ hsame row orderRead ∨
                    hsame row sealRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W DA selectorRead ∧
              Cont selectorRead J orderRead ∧ Cont orderRead E sealRead ∧
                Cont sealRead P publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
                                      (Or.inr source.left)))))))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, selectorRoute, orderRoute, sealRoute, publicRoute, publicPkg⟩
  }
  exact ⟨cert, selectorUnary, orderUnary, sealUnary, publicUnary⟩

end BEDC.Derived.RegularCauchyMinUp
