import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_readback_boundary
    {Z S M R Q H C P N streamRead regseqRead realRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont S M streamRead ->
        Cont streamRead Q regseqRead ->
          Cont regseqRead R realRead ->
            Cont N Q refusalRead ->
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory streamRead ∧ UnaryHistory regseqRead ∧
                  UnaryHistory realRead ∧ UnaryHistory refusalRead ∧ hsame H (append Z S) ∧
                    Cont S M streamRead ∧ Cont streamRead Q regseqRead ∧
                      Cont regseqRead R realRead ∧ Cont N Q refusalRead ∧ Cont M R Q ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame UnaryHistory
  intro packet streamRoute regseqRoute realRoute refusalRoute
  have carrier := packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryStream : UnaryHistory streamRead :=
    unary_cont_closed unaryS unaryM streamRoute
  have unaryRegseq : UnaryHistory regseqRead :=
    unary_cont_closed unaryStream unaryQ regseqRoute
  have unaryReal : UnaryHistory realRead :=
    unary_cont_closed unaryRegseq unaryR realRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrier
  have unaryN : UnaryHistory N :=
    routeClosure.right.right.left
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryStream, unaryRegseq, unaryReal,
      unaryRefusal, sameH, streamRoute, regseqRoute, realRoute, refusalRoute, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
