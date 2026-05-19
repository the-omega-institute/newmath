import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_zero_strip_depth_lock
    {Z S M R Q H C P N zeroStripRead depthRead lockedRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont M R depthRead ->
          Cont zeroStripRead depthRead lockedRead ->
            SemanticNameCert
                (fun row : BHist => hsame row lockedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row lockedRead ∧ Cont Z S zeroStripRead ∧ Cont M R depthRead)
                (fun row : BHist =>
                  hsame row lockedRead ∧ Cont zeroStripRead depthRead lockedRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory zeroStripRead ∧ UnaryHistory depthRead ∧
                  UnaryHistory lockedRead ∧ hsame H (append Z S) ∧
                    Cont Z S zeroStripRead ∧ Cont M R depthRead ∧
                      Cont zeroStripRead depthRead lockedRead ∧ Cont M R Q ∧
                        Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripCont depthCont lockCont
  have carrierPacket := packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure carrierPacket
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripCont
  have depthUnary : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthCont
  have lockedUnary : UnaryHistory lockedRead :=
    unary_cont_closed zeroStripUnary depthUnary lockCont
  have sourceAtLock : hsame lockedRead lockedRead ∧ UnaryHistory lockedRead :=
    ⟨hsame_refl lockedRead, lockedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row lockedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row lockedRead ∧ Cont Z S zeroStripRead ∧ Cont M R depthRead)
          (fun row : BHist =>
            hsame row lockedRead ∧ Cont zeroStripRead depthRead lockedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro lockedRead sourceAtLock
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
      exact ⟨source.left, zeroStripCont, depthCont⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, lockCont⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, zeroStripUnary, depthUnary, lockedUnary,
      routeClosure.right.right.right, zeroStripCont, depthCont, lockCont, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
