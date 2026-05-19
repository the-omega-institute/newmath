import BEDC.Derived.CriticalLineWitnessUp.RootDownstreamPackage

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_downstream_consumer_unblock
    {Z S M R Q H C P N rootRead downstream : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont (append Z S) Q rootRead →
        Cont rootRead N downstream →
          SemanticNameCert
              (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
              (fun row : BHist => hsame row downstream)
              (fun row : BHist => hsame row downstream ∧ Cont rootRead N downstream)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory N ∧
              UnaryHistory rootRead ∧ UnaryHistory downstream ∧ hsame H (append Z S) ∧
                Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                  Cont (append Z S) Q rootRead ∧ Cont rootRead N downstream := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet rootRoute downstreamRoute
  have downstreamPackage :=
    CriticalLineWitnessCarrier_root_downstream_package packet rootRoute downstreamRoute
  obtain ⟨unaryZ, unaryS, unaryQ, unaryN, rootUnary, downstreamUnary, sameH, routeQ,
    routeC, routeN, rootRouteKeep, downstreamRouteKeep⟩ := downstreamPackage
  have sourceAtDownstream : hsame downstream downstream ∧ UnaryHistory downstream :=
    ⟨hsame_refl downstream, downstreamUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row downstream ∧ UnaryHistory row)
          (fun row : BHist => hsame row downstream)
          (fun row : BHist => hsame row downstream ∧ Cont rootRead N downstream)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro downstream sourceAtDownstream
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
      exact ⟨source.left, downstreamRouteKeep⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryN, rootUnary, downstreamUnary, sameH, routeQ,
      routeC, routeN, rootRouteKeep, downstreamRouteKeep⟩

end BEDC.Derived.CriticalLineWitnessUp
