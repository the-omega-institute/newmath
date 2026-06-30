import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverRegularCauchyBridgeWindow [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead streamWindow regularReadback coverRead sealRead
      compactRead uniformRead budgetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg ->
      Cont L U endpointRead ->
        Cont W Q streamWindow ->
          Cont streamWindow R regularReadback ->
            Cont regularReadback V coverRead ->
              Cont coverRead A sealRead ->
                Cont endpointRead sealRead compactRead ->
                  Cont compactRead N uniformRead ->
                    Cont uniformRead P budgetRead ->
                      PkgSig bundle budgetRead pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row Q ∨
                                hsame row R ∨ hsame row V ∨ hsame row A ∨ hsame row N ∨
                                  hsame row P ∨ hsame row budgetRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont L U endpointRead ∧
                                Cont W Q streamWindow ∧ Cont streamWindow R regularReadback ∧
                                  Cont regularReadback V coverRead ∧
                                    Cont coverRead A sealRead ∧
                                      Cont endpointRead sealRead compactRead ∧
                                        Cont compactRead N uniformRead ∧
                                          Cont uniformRead P budgetRead ∧
                                            PkgSig bundle budgetRead pkg)
                            hsame ∧ UnaryHistory streamWindow ∧
                          UnaryHistory regularReadback ∧ UnaryHistory budgetRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface endpointRoute streamRoute regularRoute coverRoute sealRoute compactRoute
    uniformRoute budgetRoute budgetPkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have pUnary : UnaryHistory P :=
    surface.right.right.right.right.right.right.right.right.right.right.left
  have nUnary : UnaryHistory N :=
    surface.right.right.right.right.right.right.right.right.right.right.right.left
  have endpointUnary : UnaryHistory endpointRead :=
    unary_cont_closed lUnary uUnary endpointRoute
  have streamUnary : UnaryHistory streamWindow :=
    unary_cont_closed wUnary qUnary streamRoute
  have regularUnary : UnaryHistory regularReadback :=
    unary_cont_closed streamUnary rUnary regularRoute
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed regularUnary vUnary coverRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed coverUnary aUnary sealRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed endpointUnary sealUnary compactRoute
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary nUnary uniformRoute
  have budgetUnary : UnaryHistory budgetRead :=
    unary_cont_closed uniformUnary pUnary budgetRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row budgetRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row W ∨ hsame row Q ∨ hsame row R ∨
              hsame row V ∨ hsame row A ∨ hsame row N ∨ hsame row P ∨
                hsame row budgetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont W Q streamWindow ∧
              Cont streamWindow R regularReadback ∧ Cont regularReadback V coverRead ∧
                Cont coverRead A sealRead ∧ Cont endpointRead sealRead compactRead ∧
                  Cont compactRead N uniformRead ∧ Cont uniformRead P budgetRead ∧
                    PkgSig bundle budgetRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro budgetRead ⟨hsame_refl budgetRead, budgetUnary⟩
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
      exact
        ⟨source.right, endpointRoute, streamRoute, regularRoute, coverRoute, sealRoute,
          compactRoute, uniformRoute, budgetRoute, budgetPkg⟩
  }
  exact ⟨cert, streamUnary, regularUnary, budgetUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
