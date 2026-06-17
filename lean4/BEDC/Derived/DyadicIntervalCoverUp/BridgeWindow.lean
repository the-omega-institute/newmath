import BEDC.Derived.DyadicIntervalCoverUp.RootWindowCoverage

namespace BEDC.Derived.DyadicIntervalCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem DyadicIntervalCoverBridgeWindow [AskSetup] [PackageSetup]
    {L U M R V W Q A H C P N endpointRead windowRead readbackRead coverRead sealRead
      subcoverRead realHandoffRead ledgerRead bridgeWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    DyadicIntervalCoverRootObligationSurface L U M R V W Q A H C P N bundle pkg ->
      Cont L U endpointRead ->
        Cont W Q windowRead ->
          Cont windowRead R readbackRead ->
            Cont readbackRead V coverRead ->
              Cont coverRead A sealRead ->
                Cont endpointRead sealRead subcoverRead ->
                  Cont sealRead P realHandoffRead ->
                    Cont coverRead R ledgerRead ->
                      Cont realHandoffRead ledgerRead bridgeWindow ->
                        PkgSig bundle bridgeWindow pkg ->
                          SemanticNameCert
                              (fun row : BHist => hsame row bridgeWindow ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row L ∨ hsame row U ∨ hsame row M ∨
                                  hsame row R ∨ hsame row V ∨ hsame row W ∨
                                    hsame row Q ∨ hsame row A ∨ hsame row H ∨
                                      hsame row C ∨ hsame row P ∨ hsame row N ∨
                                        hsame row bridgeWindow)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont L U endpointRead ∧
                                  Cont W Q windowRead ∧
                                    Cont windowRead R readbackRead ∧
                                      Cont readbackRead V coverRead ∧
                                        Cont coverRead A sealRead ∧
                                          Cont endpointRead sealRead subcoverRead ∧
                                            Cont sealRead P realHandoffRead ∧
                                              Cont coverRead R ledgerRead ∧
                                                Cont realHandoffRead ledgerRead bridgeWindow ∧
                                                  PkgSig bundle bridgeWindow pkg)
                              hsame ∧
                            UnaryHistory bridgeWindow := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface endpointRoute windowRoute readbackRoute coverRoute sealRoute subcoverRoute
    realHandoffRoute ledgerRoute bridgeRoute bridgePkg
  have lUnary : UnaryHistory L := surface.left
  have uUnary : UnaryHistory U := surface.right.left
  have rUnary : UnaryHistory R := surface.right.right.right.left
  have vUnary : UnaryHistory V := surface.right.right.right.right.left
  have wUnary : UnaryHistory W := surface.right.right.right.right.right.left
  have qUnary : UnaryHistory Q := surface.right.right.right.right.right.right.left
  have aUnary : UnaryHistory A := surface.right.right.right.right.right.right.right.left
  have pUnary : UnaryHistory P :=
    surface.right.right.right.right.right.right.right.right.right.right.left
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
  have realHandoffUnary : UnaryHistory realHandoffRead :=
    unary_cont_closed sealUnary pUnary realHandoffRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed coverUnary rUnary ledgerRoute
  have bridgeUnary : UnaryHistory bridgeWindow :=
    unary_cont_closed realHandoffUnary ledgerUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row M ∨ hsame row R ∨ hsame row V ∨
              hsame row W ∨ hsame row Q ∨ hsame row A ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row bridgeWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U endpointRead ∧ Cont W Q windowRead ∧
              Cont windowRead R readbackRead ∧ Cont readbackRead V coverRead ∧
                Cont coverRead A sealRead ∧ Cont endpointRead sealRead subcoverRead ∧
                  Cont sealRead P realHandoffRead ∧ Cont coverRead R ledgerRead ∧
                    Cont realHandoffRead ledgerRead bridgeWindow ∧
                      PkgSig bundle bridgeWindow pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeWindow ⟨hsame_refl bridgeWindow, bridgeUnary⟩
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
          subcoverRoute, realHandoffRoute, ledgerRoute, bridgeRoute, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.DyadicIntervalCoverUp
