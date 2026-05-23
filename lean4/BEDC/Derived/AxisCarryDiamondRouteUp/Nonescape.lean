import BEDC.Derived.AxisCarryDiamondRouteUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AxisCarryDiamondRouteUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.Meta.TasteGate

theorem AxisCarryDiamondRouteNonescape
    {a b c n rho0 rho1 nu0 nu1 eta H C P N leftRead rightRead : BHist} :
    Cont rho0 eta leftRead ->
      Cont rho1 eta rightRead ->
        SemanticNameCert
            (fun row : BHist =>
              hsame row N ∧
                FieldFaithful.fields
                  (AxisCarryDiamondRouteUp.mk a b c n rho0 rho1 nu0 nu1 eta H C P N) =
                  [a, b, c, n, rho0, rho1, nu0, nu1, eta, H, C, P, N])
            (fun row : BHist =>
              hsame row rho0 ∨ hsame row rho1 ∨ hsame row n ∨ hsame row eta ∨
                hsame row N)
            (fun row : BHist =>
              hsame row N ∧ Cont rho0 eta leftRead ∧ Cont rho1 eta rightRead)
            hsame ∧
          FieldFaithful.fields
              (AxisCarryDiamondRouteUp.mk a b c n rho0 rho1 nu0 nu1 eta H C P N) =
            [a, b, c, n, rho0, rho1, nu0, nu1, eta, H, C, P, N] ∧
          hsame n n ∧ hsame eta eta ∧ Cont rho0 eta leftRead ∧
            Cont rho1 eta rightRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert FieldFaithful
  intro leftRoute rightRoute
  have fields_eq :
      FieldFaithful.fields
          (AxisCarryDiamondRouteUp.mk a b c n rho0 rho1 nu0 nu1 eta H C P N) =
        [a, b, c, n, rho0, rho1, nu0, nu1, eta, H, C, P, N] := by
    rfl
  have sourceName :
      (fun row : BHist =>
        hsame row N ∧
          FieldFaithful.fields
            (AxisCarryDiamondRouteUp.mk a b c n rho0 rho1 nu0 nu1 eta H C P N) =
            [a, b, c, n, rho0, rho1, nu0, nu1, eta, H, C, P, N]) N := by
    exact ⟨hsame_refl N, fields_eq⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row N ∧
            FieldFaithful.fields
              (AxisCarryDiamondRouteUp.mk a b c n rho0 rho1 nu0 nu1 eta H C P N) =
              [a, b, c, n, rho0, rho1, nu0, nu1, eta, H, C, P, N])
        (fun row : BHist =>
          hsame row rho0 ∨ hsame row rho1 ∨ hsame row n ∨ hsame row eta ∨
            hsame row N)
        (fun row : BHist =>
          hsame row N ∧ Cont rho0 eta leftRead ∧ Cont rho1 eta rightRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N sourceName
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
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, leftRoute, rightRoute⟩
    }
  exact
    ⟨cert, fields_eq, hsame_refl n, hsame_refl eta, leftRoute, rightRoute⟩

end BEDC.Derived.AxisCarryDiamondRouteUp
