import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_rh_consumer_boundary
    {Z S M R Q H C P N rootRead modulusRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z M rootRead ->
        Cont M R modulusRead ->
          Cont rootRead modulusRead consumerRead ->
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row consumerRead)
                (fun row : BHist =>
                  hsame row consumerRead ∧ Cont rootRead modulusRead consumerRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory rootRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory consumerRead ∧ hsame H (append Z S) ∧
                    Cont Z M rootRead ∧ Cont M R modulusRead ∧
                      Cont rootRead modulusRead consumerRead ∧ Cont Q H C ∧
                        Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet rootRoute modulusRoute consumerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryZ unaryM rootRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed rootUnary modulusUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
              hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row consumerRead)
          (fun row : BHist =>
            hsame row consumerRead ∧ Cont rootRead modulusRead consumerRead)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, consumerRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, rootUnary, modulusUnary,
      consumerUnary, sameH, rootRoute, modulusRoute, consumerRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
