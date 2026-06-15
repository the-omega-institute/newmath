import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_namecert_route_exhaustion
    {Z S M R Q H C P N routeRead nameRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S routeRead ->
        Cont routeRead N nameRead ->
          SemanticNameCert
              (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row nameRead)
              (fun row : BHist => hsame row nameRead ∧ Cont routeRead N nameRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
              UnaryHistory routeRead ∧ UnaryHistory nameRead ∧ hsame H (append Z S) ∧
                Cont Z S routeRead ∧ Cont routeRead N nameRead ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory CriticalLineWitnessCarrier
  intro packet routeReadCont nameReadCont
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed unaryZ unaryS routeReadCont
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed routeReadUnary routeClosure.right.right.left nameReadCont
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row nameRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row nameRead)
          (fun row : BHist => hsame row nameRead ∧ Cont routeRead N nameRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨hsame_refl nameRead, nameReadUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, nameReadCont⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, routeClosure.left, routeClosure.right.right.left, routeReadUnary,
      nameReadUnary, routeClosure.right.right.right, routeReadCont, nameReadCont, routeQ,
      routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
