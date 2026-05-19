import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_route_exposure
    {Z S M R Q H C P N stripRead modulusRead refusalRead sourceLock routeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q modulusRead ->
          Cont N Q refusalRead ->
            Cont modulusRead refusalRead sourceLock ->
              Cont sourceLock C routeRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row routeRead ∧ Cont Z S stripRead ∧ Cont N Q refusalRead)
                    (fun row : BHist => hsame row routeRead ∧ Cont sourceLock C routeRead)
                    hsame ∧
                  UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧
                    UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory refusalRead ∧ UnaryHistory sourceLock ∧
                        UnaryHistory routeRead ∧ hsame H (append Z S) ∧
                          Cont Z S stripRead ∧ Cont stripRead Q modulusRead ∧
                            Cont N Q refusalRead ∧ Cont modulusRead refusalRead sourceLock ∧
                              Cont sourceLock C routeRead ∧ Cont M R Q ∧ Cont Q H C ∧
                                Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute refusalRoute sourceLockRoute routeReadRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, routeN⟩ :=
    packet
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed stripUnary routeClosure.left modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  have sourceLockUnary : UnaryHistory sourceLock :=
    unary_cont_closed modulusUnary refusalUnary sourceLockRoute
  have routeReadUnary : UnaryHistory routeRead :=
    unary_cont_closed sourceLockUnary routeClosure.right.left routeReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row routeRead ∧ Cont Z S stripRead ∧ Cont N Q refusalRead)
          (fun row : BHist => hsame row routeRead ∧ Cont sourceLock C routeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead ⟨hsame_refl routeRead, routeReadUnary⟩
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
      exact ⟨source.left, stripRoute, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, routeReadRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, routeClosure.left, stripUnary, modulusUnary, refusalUnary,
      sourceLockUnary, routeReadUnary, routeClosure.right.right.right, stripRoute,
      modulusRoute, refusalRoute, sourceLockRoute, routeReadRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
