import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_finite_source_lattice_boundary
    {Z S M R Q H C P N sourceRead comparisonRead latticeRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S sourceRead ->
        Cont M R comparisonRead ->
          Cont sourceRead comparisonRead latticeRead ->
            SemanticNameCert
                (fun row : BHist => hsame row latticeRead ∧ UnaryHistory row)
                (fun row : BHist => hsame row latticeRead)
                (fun row : BHist =>
                  hsame row latticeRead ∧ Cont sourceRead comparisonRead latticeRead)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                  UnaryHistory sourceRead ∧ UnaryHistory comparisonRead ∧
                    UnaryHistory latticeRead ∧ hsame H (append Z S) ∧
                      Cont Z S sourceRead ∧ Cont M R comparisonRead ∧
                        Cont sourceRead comparisonRead latticeRead ∧ Cont M R Q ∧
                          Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet sourceRoute comparisonRoute latticeRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed unaryZ unaryS sourceRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed unaryM unaryR comparisonRoute
  have latticeUnary : UnaryHistory latticeRead :=
    unary_cont_closed sourceUnary comparisonUnary latticeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row latticeRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row latticeRead)
          (fun row : BHist => hsame row latticeRead ∧ Cont sourceRead comparisonRead latticeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro latticeRead ⟨hsame_refl latticeRead, latticeUnary⟩
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
      exact ⟨source.left, latticeRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, sourceUnary,
      comparisonUnary, latticeUnary, sameH, sourceRoute, comparisonRoute, latticeRoute,
      routeQ, routeC, routeN⟩

theorem CriticalLineWitnessFiniteSourceLatticeBoundary
    {Z S M R Q H C P N zetaRead modulusRead rootRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zetaRead ->
        Cont zetaRead Q modulusRead ->
          Cont (append Z S) Q rootRead ->
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
              UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory N ∧
                UnaryHistory zetaRead ∧ UnaryHistory modulusRead ∧ UnaryHistory rootRead ∧
                  hsame H (append Z S) ∧ Cont Z S zetaRead ∧
                    Cont zetaRead Q modulusRead ∧ Cont (append Z S) Q rootRead ∧
                      Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet zetaRoute modulusRoute rootRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have zetaUnary : UnaryHistory zetaRead :=
    unary_cont_closed unaryZ unaryS zetaRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed zetaUnary routeClosure.left modulusRoute
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary routeClosure.left rootRoute
  exact
    ⟨unaryZ, unaryS, unaryM, unaryR, routeClosure.left, unaryH, routeClosure.right.left,
      routeClosure.right.right.left, zetaUnary, modulusUnary, rootUnary,
      routeClosure.right.right.right, zetaRoute, modulusRoute, rootRoute, routeQ, routeC,
      routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
