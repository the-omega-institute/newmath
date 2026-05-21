import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootNameCertConsumerTotality
    {Z S M R Q H C P N consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N P consumerRead ->
        SemanticNameCert
            (fun row : BHist => hsame row consumerRead /\ UnaryHistory row)
            (fun row : BHist => hsame row consumerRead /\ Cont C P N)
            (fun row : BHist => hsame row consumerRead /\ Cont N P consumerRead)
            hsame /\
          UnaryHistory Z /\ UnaryHistory S /\ UnaryHistory M /\ UnaryHistory R /\
            UnaryHistory Q /\ UnaryHistory C /\ UnaryHistory N /\ UnaryHistory consumerRead /\
              hsame H (append Z S) /\ Cont M R Q /\ Cont Q H C /\ Cont C P N /\
                Cont N P consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet consumerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed unaryN unaryP consumerRoute
  have sourceAtConsumer : hsame consumerRead consumerRead /\ UnaryHistory consumerRead :=
    ⟨hsame_refl consumerRead, consumerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead /\ UnaryHistory row)
          (fun row : BHist => hsame row consumerRead /\ Cont C P N)
          (fun row : BHist => hsame row consumerRead /\ Cont N P consumerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead sourceAtConsumer
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
      exact ⟨source.left, routeN⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryC, unaryN, consumerUnary, sameH,
      routeQ, routeC, routeN, consumerRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
