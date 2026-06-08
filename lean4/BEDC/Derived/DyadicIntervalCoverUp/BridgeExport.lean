import BEDC.Derived.DyadicIntervalCoverUp.FiniteCoverBridgeScope

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverBridgeExport [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead readbackRead coverRead sealRead
      subcoverRead namedRead publicRead budgetRead bridgeRead exportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg ->
      Cont L U endpointRead ->
        Cont W Q windowRead ->
          Cont windowRead R readbackRead ->
            Cont readbackRead V coverRead ->
              Cont coverRead A sealRead ->
                Cont endpointRead sealRead subcoverRead ->
                  Cont subcoverRead N namedRead ->
                    Cont namedRead P publicRead ->
                      Cont publicRead N budgetRead ->
                        Cont budgetRead C bridgeRead ->
                          Cont bridgeRead N exportRead ->
                            PkgSig bundle exportRead pkg ->
                              SemanticNameCert
                                  (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row L ∨ hsame row U ∨ hsame row M ∨
                                      hsame row R ∨ hsame row V ∨ hsame row W ∨
                                        hsame row Q ∨ hsame row A ∨ hsame row H ∨
                                          hsame row C ∨ hsame row P ∨ hsame row N ∨
                                            hsame row exportRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont L U endpointRead ∧
                                      Cont W Q windowRead ∧
                                        Cont windowRead R readbackRead ∧
                                          Cont readbackRead V coverRead ∧
                                            Cont coverRead A sealRead ∧
                                              Cont endpointRead sealRead subcoverRead ∧
                                                Cont subcoverRead N namedRead ∧
                                                  Cont namedRead P publicRead ∧
                                                    Cont publicRead N budgetRead ∧
                                                      Cont budgetRead C bridgeRead ∧
                                                        Cont bridgeRead N exportRead ∧
                                                          PkgSig bundle exportRead pkg)
                                  hsame ∧
                                UnaryHistory exportRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface endpointRoute windowRoute readbackRoute coverRoute sealRoute subcoverRoute
    namedRoute publicRoute budgetRoute bridgeRoute exportRoute exportPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have cUnary : UnaryHistory C :=
    surface.right.right.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed wUnary qUnary windowRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed windowUnary rUnary readbackRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed readbackUnary vUnary coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have subcoverUnary : UnaryHistory subcoverRead :=
    unary_cont_closed endpointUnary sealUnary subcoverRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed subcoverUnary nUnary namedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed namedUnary surface.right.right.right.right.right.right.right.right.right.right.left
      publicRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed publicUnary nUnary budgetRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed budgetUnary cUnary bridgeRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed bridgeUnary nUnary exportRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row exportRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row exportRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont W Q windowRead ∧
              Cont windowRead R readbackRead ∧ Cont readbackRead V coverRead ∧
                Cont coverRead A sealRead ∧ Cont endpointRead sealRead subcoverRead ∧
                  Cont subcoverRead N namedRead ∧ Cont namedRead P publicRead ∧
                    Cont publicRead N budgetRead ∧ Cont budgetRead C bridgeRead ∧
                      Cont bridgeRead N exportRead ∧ PkgSig bundle exportRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro exportRead ⟨hsame_refl exportRead, exportUnary⟩
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
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, endpointRoute, windowRoute, readbackRoute, coverRoute, sealRoute,
          subcoverRoute, namedRoute, publicRoute, budgetRoute, bridgeRoute, exportRoute,
          exportPkg⟩
  }
  exact ⟨cert, exportUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
