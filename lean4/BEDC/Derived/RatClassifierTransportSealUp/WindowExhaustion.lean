import BEDC.Derived.RatClassifierTransportSealUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Unary

namespace BEDC.Derived.RatClassifierTransportSealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem RatClassifierTransportSealCarrier_window_exhaustion
    {Q S W D A H C N realRead : BHist} :
    FieldFaithful.fields (RatClassifierTransportSealUp.mk Q S W D A H C N) =
      [Q, S, W, D, A, H, C, N] →
      UnaryHistory Q →
        UnaryHistory S →
          UnaryHistory D →
            UnaryHistory H →
              Cont Q S W →
                Cont W D A →
                  Cont A H realRead →
                    UnaryHistory W ∧ UnaryHistory A ∧ UnaryHistory realRead ∧
                      Cont Q S W ∧ Cont W D A ∧ Cont A H realRead := by
  -- BEDC touchpoint anchor: BHist FieldFaithful Cont UnaryHistory
  intro fields unaryQ unaryS unaryD unaryH routeQS routeWD routeAH
  cases fields
  have unaryW : UnaryHistory W :=
    unary_cont_closed unaryQ unaryS routeQS
  have unaryA : UnaryHistory A :=
    unary_cont_closed unaryW unaryD routeWD
  have unaryReal : UnaryHistory realRead :=
    unary_cont_closed unaryA unaryH routeAH
  exact ⟨unaryW, unaryA, unaryReal, routeQS, routeWD, routeAH⟩

end BEDC.Derived.RatClassifierTransportSealUp
