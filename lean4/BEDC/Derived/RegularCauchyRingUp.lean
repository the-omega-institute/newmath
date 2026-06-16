import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
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

theorem RegularCauchyRingCarrier_namecert_obligations
    {A B WA WB DA DB ES EG EM EL H C P N : BHist} :
    RegularCauchyRingCarrier A B WA WB DA DB ES EG EM EL H C P N ->
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row A ∨ hsame row B ∨ hsame row WA ∨ hsame row WB ∨ hsame row DA ∨
              hsame row DB ∨ hsame row ES ∨ hsame row EG ∨ hsame row EM ∨ hsame row EL ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => UnaryHistory row ∧ Cont A WA DA ∧ Cont B WB DB ∧ Cont H C P)
          hsame ∧ UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory WA ∧ UnaryHistory WB ∧
        UnaryHistory DA ∧ UnaryHistory DB ∧ UnaryHistory ES ∧ UnaryHistory EG ∧
          UnaryHistory EM ∧ UnaryHistory EL ∧ Cont A WA DA ∧ Cont B WB DB ∧ Cont H C P := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier
  obtain ⟨unaryA, unaryB, unaryWA, unaryWB, unaryDA, unaryDB, unaryES, unaryEG, unaryEM,
    unaryEL, _unaryH, _unaryC, _unaryP, unaryN, routeDA, routeDB, routeP⟩ := carrier
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro N ⟨hsame_refl N, unaryN⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr
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
                                (Or.inr sourceRow.left))))))))))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨sourceRow.right, routeDA, routeDB, routeP⟩
    }
  · exact
      ⟨unaryA, unaryB, unaryWA, unaryWB, unaryDA, unaryDB, unaryES, unaryEG, unaryEM, unaryEL,
        routeDA, routeDB, routeP⟩

end BEDC.Derived.RegularCauchyRingUp
