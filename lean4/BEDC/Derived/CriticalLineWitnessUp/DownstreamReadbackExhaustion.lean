import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_downstream_readback_exhaustion
    {Z S M R Q H C P N stripRead modulusRead refusalRead sourceLock routeRead
      downstreamRead readback : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont stripRead Q modulusRead ->
          Cont N Q refusalRead ->
            Cont modulusRead refusalRead sourceLock ->
              Cont sourceLock C routeRead ->
                Cont routeRead P downstreamRead ->
                  Cont downstreamRead N readback ->
                    SemanticNameCert
                        (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row readback ∧ Cont Z S stripRead ∧
                            Cont N Q refusalRead)
                        (fun row : BHist =>
                          hsame row readback ∧ Cont downstreamRead N readback)
                        hsame ∧
                      UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧
                        UnaryHistory stripRead ∧ UnaryHistory modulusRead ∧
                          UnaryHistory refusalRead ∧ UnaryHistory sourceLock ∧
                            UnaryHistory routeRead ∧ UnaryHistory downstreamRead ∧
                              UnaryHistory readback ∧ hsame H (append Z S) ∧
                                Cont Z S stripRead ∧ Cont stripRead Q modulusRead ∧
                                  Cont N Q refusalRead ∧
                                    Cont modulusRead refusalRead sourceLock ∧
                                      Cont sourceLock C routeRead ∧
                                        Cont routeRead P downstreamRead ∧
                                          Cont downstreamRead N readback ∧
                                            Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet stripRoute modulusRoute refusalRoute sourceLockRoute routeReadRoute
    downstreamRoute readbackRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have unaryStrip : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have unaryModulus : UnaryHistory modulusRead :=
    unary_cont_closed unaryStrip unaryQ modulusRoute
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unarySourceLock : UnaryHistory sourceLock :=
    unary_cont_closed unaryModulus unaryRefusal sourceLockRoute
  have unaryRouteRead : UnaryHistory routeRead :=
    unary_cont_closed unarySourceLock unaryC routeReadRoute
  have unaryDownstream : UnaryHistory downstreamRead :=
    unary_cont_closed unaryRouteRead unaryP downstreamRoute
  have unaryReadback : UnaryHistory readback :=
    unary_cont_closed unaryDownstream unaryN readbackRoute
  have sourceAtReadback :
      hsame readback readback ∧ UnaryHistory readback :=
    ⟨hsame_refl readback, unaryReadback⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row readback ∧ Cont Z S stripRead ∧ Cont N Q refusalRead)
          (fun row : BHist =>
            hsame row readback ∧ Cont downstreamRead N readback)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback sourceAtReadback
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
      exact ⟨source.left, readbackRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryStrip, unaryModulus, unaryRefusal,
      unarySourceLock, unaryRouteRead, unaryDownstream, unaryReadback, sameH, stripRoute,
      modulusRoute, refusalRoute, sourceLockRoute, routeReadRoute, downstreamRoute,
      readbackRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
