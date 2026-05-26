import BEDC.Derived.RegularCauchyZeroUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyZeroUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def RegularCauchyZeroCarrier
    (q s r m mu e h c p n : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame append
  UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory r ∧ UnaryHistory m ∧
    UnaryHistory mu ∧ UnaryHistory e ∧ UnaryHistory c ∧ UnaryHistory p ∧ UnaryHistory n ∧
      Cont q s r ∧ Cont r m mu ∧ Cont mu e c ∧ hsame h (append q s)

theorem RegularCauchyZeroCarrier_real_seal_nonescape
    {q s r m mu e h c p n sealRead : BHist} :
    RegularCauchyZeroCarrier q s r m mu e h c p n ->
      Cont mu e sealRead ->
        UnaryHistory q ∧ UnaryHistory s ∧ UnaryHistory r ∧ UnaryHistory m ∧
          UnaryHistory mu ∧ UnaryHistory e ∧ UnaryHistory sealRead ∧
            Cont q s r ∧ Cont r m mu ∧ Cont mu e sealRead ∧ hsame h (append q s) := by
  -- BEDC touchpoint anchor: BHist Cont hsame append UnaryHistory
  intro carrier sealRoute
  obtain ⟨qUnary, sUnary, rUnary, mUnary, muUnary, eUnary, _cUnary, _pUnary, _nUnary,
    qrRoute, rmRoute, _carrierSealRoute, transportSame⟩ := carrier
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed muUnary eUnary sealRoute
  exact
    ⟨qUnary, sUnary, rUnary, mUnary, muUnary, eUnary, sealReadUnary, qrRoute,
      rmRoute, sealRoute, transportSame⟩

end BEDC.Derived.RegularCauchyZeroUp
