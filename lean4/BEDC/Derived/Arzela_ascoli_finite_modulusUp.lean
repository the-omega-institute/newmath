import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Unary

namespace BEDC.Derived.Arzela_ascoli_finite_modulusUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ArzelaAscoliFiniteModulusCarrier (K F M W R E H C P N : BHist) : Prop :=
  UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory M ∧ UnaryHistory W ∧
    UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory P ∧ hsame H (append K F) ∧
      Cont M W R ∧ Cont R E C ∧ Cont C P N

theorem ArzelaAscoliFiniteModulusCompactmetricForwardRoute
    {K F M W R E H C P N compactRead equicontRead modulusRead sealRead : BHist} :
    ArzelaAscoliFiniteModulusCarrier K F M W R E H C P N ->
      Cont K F compactRead ->
        Cont compactRead M equicontRead ->
          Cont equicontRead W modulusRead ->
            Cont modulusRead E sealRead ->
              UnaryHistory compactRead ∧ UnaryHistory equicontRead ∧
                UnaryHistory modulusRead ∧ UnaryHistory sealRead ∧ hsame H (append K F) ∧
                  Cont K F compactRead ∧ Cont compactRead M equicontRead ∧
                    Cont equicontRead W modulusRead ∧ Cont modulusRead E sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier compactRoute equicontRoute modulusRoute sealRoute
  obtain ⟨kUnary, fUnary, mUnary, wUnary, _rUnary, eUnary, _pUnary, sameH,
    _routeR, _routeC, _routeN⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed kUnary fUnary compactRoute
  have equicontUnary : UnaryHistory equicontRead :=
    unary_cont_closed compactUnary mUnary equicontRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed equicontUnary wUnary modulusRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed modulusUnary eUnary sealRoute
  exact
    ⟨compactUnary, equicontUnary, modulusUnary, sealUnary, sameH, compactRoute,
      equicontRoute, modulusRoute, sealRoute⟩

end BEDC.Derived.Arzela_ascoli_finite_modulusUp
