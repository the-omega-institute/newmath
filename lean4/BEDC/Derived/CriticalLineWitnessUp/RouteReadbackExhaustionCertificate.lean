import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_route_readback_exhaustion_certificate
    {Z S M R Q H C P N zeroStripRead reflectionRead downstreamRead readback : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont zeroStripRead H reflectionRead ->
          Cont N Q downstreamRead ->
            Cont reflectionRead downstreamRead readback ->
              SemanticNameCert
                  (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row readback ∧ Cont Z S zeroStripRead ∧
                      Cont N Q downstreamRead)
                  (fun row : BHist =>
                    hsame row readback ∧ Cont reflectionRead downstreamRead readback)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
                  UnaryHistory N ∧ UnaryHistory zeroStripRead ∧
                    UnaryHistory reflectionRead ∧ UnaryHistory downstreamRead ∧
                      UnaryHistory readback ∧ hsame H (append Z S) ∧
                        Cont Z S zeroStripRead ∧ Cont zeroStripRead H reflectionRead ∧
                          Cont N Q downstreamRead ∧
                            Cont reflectionRead downstreamRead readback ∧ Cont M R Q ∧
                              Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute reflectionRoute downstreamRoute readbackRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have reflectionUnary : UnaryHistory reflectionRead :=
    unary_cont_closed zeroStripUnary unaryH reflectionRoute
  have downstreamUnary : UnaryHistory downstreamRead :=
    unary_cont_closed unaryN unaryQ downstreamRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed reflectionUnary downstreamUnary readbackRoute
  have sourceAtReadback : hsame readback readback ∧ UnaryHistory readback :=
    ⟨hsame_refl readback, readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∧ Cont Z S zeroStripRead ∧ Cont N Q downstreamRead)
          (fun row : BHist =>
            hsame row readback ∧ Cont reflectionRead downstreamRead readback)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback sourceAtReadback
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
      exact ⟨source.left, zeroStripRoute, downstreamRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, readbackRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryH, unaryN, zeroStripUnary, reflectionUnary,
      downstreamUnary, readbackUnary, sameH, zeroStripRoute, reflectionRoute,
      downstreamRoute, readbackRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
