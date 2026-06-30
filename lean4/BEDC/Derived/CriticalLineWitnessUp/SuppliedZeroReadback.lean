import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_supplied_zero_readback
    {Z S M R Q H C P N zeroRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        SemanticNameCert
            (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
            (fun row : BHist => hsame row zeroRead ∧ Cont Z S zeroRead)
            (fun row : BHist => hsame row zeroRead ∧ hsame H (append Z S))
            hsame ∧
          UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory zeroRead ∧ hsame H (append Z S) ∧
            Cont Z S zeroRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryZeroRead : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have sourceAtZero : hsame zeroRead zeroRead ∧ UnaryHistory zeroRead :=
    ⟨hsame_refl zeroRead, unaryZeroRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row zeroRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row zeroRead ∧ Cont Z S zeroRead)
          (fun row : BHist => hsame row zeroRead ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro zeroRead sourceAtZero
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
      exact ⟨source.left, zeroRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sameH⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryZeroRead, sameH, zeroRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
