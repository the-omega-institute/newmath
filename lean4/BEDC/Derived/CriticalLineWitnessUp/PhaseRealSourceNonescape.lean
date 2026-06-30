import BEDC.Derived.CriticalLineWitnessUp.PhaseRealSourceTriad

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_phase_real_source_nonescape
    {Z S M R Q H C P N stripRead phaseReal regSeq streamName sourceRead
      refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q phaseReal ->
          Cont phaseReal H regSeq ->
            Cont regSeq Q streamName ->
              Cont streamName C sourceRead ->
                Cont sourceRead N refusalRead ->
                  SemanticNameCert
                      (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row sourceRead ∨ hsame row refusalRead ∨
                          hsame row streamName)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont Z S stripRead ∧
                          Cont stripRead Q phaseReal ∧ Cont phaseReal H regSeq ∧
                            Cont regSeq Q streamName ∧ Cont streamName C sourceRead ∧
                              Cont sourceRead N refusalRead ∧ hsame H (append Z S))
                      hsame ∧
                    UnaryHistory stripRead ∧ UnaryHistory phaseReal ∧
                      UnaryHistory regSeq ∧ UnaryHistory streamName ∧
                        UnaryHistory sourceRead ∧ UnaryHistory refusalRead ∧
                          hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute phaseRealRoute regSeqRoute streamNameRoute sourceRoute refusalRoute
  have routeClosure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, _unaryM, _unaryR, _unaryP, sameH, _routeQ, _routeC,
    _routeN⟩ := packet
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have stripUnary : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have phaseRealUnary : UnaryHistory phaseReal :=
    unary_cont_closed stripUnary routeClosure.left phaseRealRoute
  have regSeqUnary : UnaryHistory regSeq :=
    unary_cont_closed phaseRealUnary unaryH regSeqRoute
  have streamNameUnary : UnaryHistory streamName :=
    unary_cont_closed regSeqUnary routeClosure.left streamNameRoute
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed streamNameUnary routeClosure.right.left sourceRoute
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed sourceReadUnary routeClosure.right.right.left refusalRoute
  have sourceAtRefusal : hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, refusalReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceRead ∨ hsame row refusalRead ∨ hsame row streamName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S stripRead ∧ Cont stripRead Q phaseReal ∧
              Cont phaseReal H regSeq ∧ Cont regSeq Q streamName ∧
                Cont streamName C sourceRead ∧ Cont sourceRead N refusalRead ∧
                  hsame H (append Z S))
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceAtRefusal
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
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, stripRoute, phaseRealRoute, regSeqRoute, streamNameRoute,
          sourceRoute, refusalRoute, sameH⟩
  }
  exact
    ⟨cert, stripUnary, phaseRealUnary, regSeqUnary, streamNameUnary, sourceReadUnary,
      refusalReadUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
