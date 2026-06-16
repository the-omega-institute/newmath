import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def RegularCauchyRingCarrier
    (A B WA WB DA DB ES EG EM EL H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory WA ∧ UnaryHistory WB ∧
    UnaryHistory DA ∧ UnaryHistory DB ∧ UnaryHistory ES ∧ UnaryHistory EG ∧
      UnaryHistory EM ∧ UnaryHistory EL ∧ UnaryHistory H ∧ UnaryHistory C ∧
        UnaryHistory P ∧ UnaryHistory N ∧ Cont A WA DA ∧ Cont B WB DB ∧ Cont H C P

theorem RegularCauchyRingOperationClosure
    {A B WA WB DA DB ES EG EM EL H C P N S G M L RS RG RM RL : BHist} :
    RegularCauchyRingCarrier A B WA WB DA DB ES EG EM EL H C P N ->
      Cont A B S ->
        Cont A WA G ->
          Cont A B M ->
            Cont A WB L ->
              Cont S ES RS ->
                Cont G EG RG ->
                  Cont M EM RM ->
                    Cont L EL RL ->
                      UnaryHistory S ∧ UnaryHistory G ∧ UnaryHistory M ∧
                        UnaryHistory L ∧ UnaryHistory RS ∧ UnaryHistory RG ∧
                          UnaryHistory RM ∧ UnaryHistory RL ∧ Cont S ES RS ∧
                            Cont G EG RG ∧ Cont M EM RM ∧ Cont L EL RL := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier sumRoute negRoute productRoute scaleRoute sumSeal negSeal productSeal scaleSeal
  obtain ⟨unaryA, unaryB, unaryWA, unaryWB, _unaryDA, _unaryDB, unaryES, unaryEG,
    unaryEM, unaryEL, _unaryH, _unaryC, _unaryP, _unaryN, _sourceWindowA,
    _sourceWindowB, _transportReplay⟩ := carrier
  have unaryS : UnaryHistory S := unary_cont_closed unaryA unaryB sumRoute
  have unaryG : UnaryHistory G := unary_cont_closed unaryA unaryWA negRoute
  have unaryM : UnaryHistory M := unary_cont_closed unaryA unaryB productRoute
  have unaryL : UnaryHistory L := unary_cont_closed unaryA unaryWB scaleRoute
  have unaryRS : UnaryHistory RS := unary_cont_closed unaryS unaryES sumSeal
  have unaryRG : UnaryHistory RG := unary_cont_closed unaryG unaryEG negSeal
  have unaryRM : UnaryHistory RM := unary_cont_closed unaryM unaryEM productSeal
  have unaryRL : UnaryHistory RL := unary_cont_closed unaryL unaryEL scaleSeal
  exact
    ⟨unaryS, unaryG, unaryM, unaryL, unaryRS, unaryRG, unaryRM, unaryRL, sumSeal,
      negSeal, productSeal, scaleSeal⟩

end BEDC.Derived.RegularCauchyRingUp
