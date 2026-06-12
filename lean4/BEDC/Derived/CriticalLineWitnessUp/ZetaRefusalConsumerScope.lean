import BEDC.Derived.CriticalLineWitnessUp.RootPhaseRealSourceUnblock
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessZetaRefusalConsumerScope
    {Z S M R Q H C P N zetaRead sourceRead realWindow refusalRead boundaryRead :
      BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead H sourceRead ->
          Cont M R realWindow ->
            Cont N Q refusalRead ->
              Cont refusalRead C boundaryRead ->
                SemanticNameCert
                    (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                        hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row N ∨
                          hsame row sourceRead ∨ hsame row boundaryRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont Z S zetaRead ∧
                        Cont zetaRead H sourceRead ∧ Cont N Q refusalRead ∧
                          Cont refusalRead C boundaryRead ∧ hsame H (append Z S))
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory boundaryRead ∧
                    hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zetaRoute sourceRoute realWindowRoute refusalRoute boundaryRoute
  have downstream :=
    CriticalLineWitnessRootDownstreamUnblockPackage packet zetaRoute sourceRoute
      realWindowRoute refusalRoute boundaryRoute
  obtain
    ⟨_unaryZ, _unaryS, _unaryM, _unaryR, _unaryQ, _unaryH, _unaryC, _unaryN,
      _unaryZetaRead, unarySourceRead, _unaryRealWindow, _unaryRefusalRead,
      unaryBoundaryRead, sameH, zetaRouteOut, sourceRouteOut, _routeQ, _realWindowRouteOut,
      _routeC, _routeN, refusalRouteOut, boundaryRouteOut⟩ := downstream
  have sourceBoundary :
      (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row) boundaryRead := by
    exact ⟨hsame_refl boundaryRead, unaryBoundaryRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row boundaryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row N ∨ hsame row sourceRead ∨
                hsame row boundaryRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S zetaRead ∧ Cont zetaRead H sourceRead ∧
              Cont N Q refusalRead ∧ Cont refusalRead C boundaryRead ∧
                hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundaryRead sourceBoundary
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, zetaRouteOut, sourceRouteOut, refusalRouteOut, boundaryRouteOut,
          sameH⟩
  }
  exact ⟨cert, unarySourceRead, unaryBoundaryRead, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
