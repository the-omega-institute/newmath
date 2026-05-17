import BEDC.Derived.ContinuationMonadUp

namespace BEDC.Derived.ContinuationMonadUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ContinuationMonadCarrier_unit_route_nonescape
    {A B C f g u H K L N unitRead : BHist} :
    ContinuationMonadCarrier A B C f g u H K L N →
      hsame unitRead u →
        Cont A unitRead A →
          SemanticNameCert
              (fun row : BHist => hsame row unitRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row unitRead ∧ Cont A unitRead A)
              (fun row : BHist => hsame row unitRead ∧ hsame N L)
              hsame ∧
            Cont A unitRead A ∧ hsame unitRead u ∧ hsame N L := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  intro carrier unitSame unitRoute
  obtain ⟨_unaryA, _unaryF, _unaryG, unaryU, _routeB, _routeC, _routeK, _routeL,
    sameEndpoint⟩ := carrier
  have unaryUnitRead : UnaryHistory unitRead :=
    unary_transport unaryU (hsame_symm unitSame)
  have sourceUnitRead :
      (fun row : BHist => hsame row unitRead ∧ UnaryHistory row) unitRead := by
    exact ⟨hsame_refl unitRead, unaryUnitRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row unitRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row unitRead ∧ Cont A unitRead A)
          (fun row : BHist => hsame row unitRead ∧ hsame N L)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro unitRead sourceUnitRead
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact And.intro (hsame_trans (hsame_symm same) source.left)
            (unary_transport source.right same)
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, unitRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, sameEndpoint⟩
    }
  exact ⟨cert, unitRoute, unitSame, sameEndpoint⟩

end BEDC.Derived.ContinuationMonadUp
