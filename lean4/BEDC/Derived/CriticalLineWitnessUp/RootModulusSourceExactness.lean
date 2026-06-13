import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_modulus_source_exactness
    {Z S M R Q H C P N sourceRead modulusRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R modulusRead ->
          Cont N Q refusalRead ->
            UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧ UnaryHistory refusalRead ∧
              hsame H (append Z S) ∧ Cont Z S sourceRead ∧ Cont M R modulusRead ∧
                Cont N Q refusalRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet sourceRoute modulusRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed routeClosure.right.right.left routeClosure.left refusalRoute
  exact
    ⟨sourceUnary, modulusUnary, refusalUnary, sameH, sourceRoute, modulusRoute,
      refusalRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessRootModulusSourceExactness
    {Z S M R Q H C P N sourceRead modulusRead consumerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont Z S sourceRead →
        Cont M R modulusRead →
          Cont sourceRead modulusRead consumerRead →
            SemanticNameCert
                (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                    hsame row Q ∨ hsame row H ∨ hsame row sourceRead ∨
                      hsame row modulusRead ∨ hsame row consumerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont Z S sourceRead ∧ Cont M R modulusRead ∧
                    Cont sourceRead modulusRead consumerRead ∧ hsame H (append Z S))
                hsame ∧
              UnaryHistory sourceRead ∧ UnaryHistory modulusRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: CriticalLineWitnessCarrier BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute modulusRoute consumerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, _routeQ, _routeC, _routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed sourceUnary modulusUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row consumerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row sourceRead ∨ hsame row modulusRead ∨
                hsame row consumerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S sourceRead ∧ Cont M R modulusRead ∧
              Cont sourceRead modulusRead consumerRead ∧ hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro consumerRead ⟨hsame_refl consumerRead, consumerUnary⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, modulusRoute, consumerRoute, sameH⟩
  }
  exact ⟨cert, sourceUnary, modulusUnary, consumerUnary⟩

end BEDC.Derived.CriticalLineWitnessUp
