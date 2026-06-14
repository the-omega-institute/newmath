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

theorem ArzelaAscoliFiniteModulusCarrier_route_closure {K F M W R E H C P N : BHist} :
    ArzelaAscoliFiniteModulusCarrier K F M W R E H C P N ->
      UnaryHistory R ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append K F) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet
  obtain ⟨_unaryK, _unaryF, unaryM, unaryW, _unaryR, unaryE, unaryP, sameH, routeR,
    routeC, routeN⟩ := packet
  have routeRUnary : UnaryHistory R :=
    unary_cont_closed unaryM unaryW routeR
  have routeCUnary : UnaryHistory C :=
    unary_cont_closed routeRUnary unaryE routeC
  have routeNUnary : UnaryHistory N :=
    unary_cont_closed routeCUnary unaryP routeN
  exact ⟨routeRUnary, routeCUnary, routeNUnary, sameH⟩

end BEDC.Derived.Arzela_ascoli_finite_modulusUp
