import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CriticalLineWitnessZetaLink {Z S M R Q H C P N zetaRead modulusRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q modulusRead ->
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory zetaRead ∧
            UnaryHistory modulusRead ∧ hsame H (append Z S) ∧ Cont Z S zetaRead ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                Cont zetaRead Q modulusRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro packet zeroStripZeta zetaModulus
  have carrierPacket := packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have closure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrierPacket
  have zetaReadUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zeroStripZeta
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed zetaReadUnary closure.left zetaModulus
  exact
    ⟨unaryZ, unaryS, closure.left, zetaReadUnary, modulusReadUnary,
      closure.right.right.right, zeroStripZeta, routeQ, routeC, routeN, zetaModulus⟩

end BEDC.Derived.CriticalLineWitnessUp
