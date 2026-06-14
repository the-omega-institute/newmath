import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_refusal_export_boundary
    {Z S M R Q H C P N fixedRead exportRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R fixedRead ->
        Cont fixedRead N exportRead ->
          SemanticNameCert
              (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row exportRead)
              (fun row : BHist => hsame row exportRead ∧ Cont fixedRead N exportRead)
              hsame ∧
            UnaryHistory fixedRead ∧ UnaryHistory exportRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert
  intro packet fixedRoute exportRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨_unaryZ, _unaryS, unaryM, unaryR, _unaryP, _sameH, _routeQ, _routeC,
      _routeN⟩ := packet
  have fixedUnary : UnaryHistory fixedRead :=
    unary_cont_closed unaryM unaryR fixedRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed fixedUnary routeClosure.right.right.left exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row exportRead)
          (fun row : BHist => hsame row exportRead ∧ Cont fixedRead N exportRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
      exact ⟨source.left, exportRoute⟩
  }
  exact ⟨cert, fixedUnary, exportUnary, routeClosure.right.right.right⟩

end BEDC.Derived.CriticalLineWitnessUp
