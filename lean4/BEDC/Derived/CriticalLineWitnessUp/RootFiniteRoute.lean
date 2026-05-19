import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_finite_strip_route
    {Z S M R Q H C P N stripRead sourceRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead H sourceRead ->
          SemanticNameCert
              (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row sourceRead)
              (fun row : BHist => hsame row sourceRead ∧ Cont stripRead H sourceRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
              UnaryHistory stripRead ∧ UnaryHistory sourceRead ∧ hsame H (append Z S) ∧
                Cont Z S stripRead ∧ Cont stripRead H sourceRead ∧ Cont M R Q ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute sourceRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport sourceUnary (hsame_symm sameH)
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed stripUnary unaryH sourceRoute
  have sourceAtRead : hsame sourceRead sourceRead ∧ UnaryHistory sourceRead :=
    ⟨hsame_refl sourceRead, sourceReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row sourceRead)
          (fun row : BHist => hsame row sourceRead ∧ Cont stripRead H sourceRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sourceRead sourceAtRead
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
      exact ⟨source.left, sourceRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryH, stripUnary, sourceReadUnary, sameH,
      stripRoute, sourceRoute, routeQ, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_root_finite_route_totality
    {Z S M R Q H C P N rootRead downstream : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont (append Z S) Q rootRead ->
        Cont rootRead N downstream ->
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
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have sourceUnary : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceUnary routeClosure.left rootRoute
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed rootUnary routeClosure.right.right.left downstreamRoute
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
      exact ⟨source.left, downstreamRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, routeClosure.left, routeClosure.right.right.left, rootUnary,
      downstreamUnary, sameH, routeQ, routeC, routeN, rootRoute, downstreamRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
