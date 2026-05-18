import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_downstream_blocker_scope [AskSetup]
    [PackageSetup] {a b c d e f g h p n selected routed blockerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame selected a ∨ hsame selected b ∨ hsame selected c ∨ hsame selected d ∨
          hsame selected e ∨ hsame selected f ∨ hsame selected g) ->
        Cont selected h routed ->
          Cont routed p blockerRead ->
            PkgSig bundle blockerRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n
                      bundle pkg ∧ hsame row blockerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧
                      (hsame row selected ∨ hsame row routed ∨ hsame row blockerRead))
                  (fun _row : BHist =>
                    Cont selected h routed ∧ Cont routed p blockerRead ∧ hsame p n ∧
                      PkgSig bundle p pkg ∧ PkgSig bundle blockerRead pkg)
                  hsame ∧ UnaryHistory selected ∧ UnaryHistory routed ∧
                    UnaryHistory blockerRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet selectedRow selectedRoute blockerRoute blockerPkg
  have packetWitness :
      AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg := packet
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, _routeCD,
      _routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have selectedUnary : UnaryHistory selected := by
    cases selectedRow with
    | inl sameA =>
        exact unary_transport_symm aUnary sameA
    | inr rest =>
        cases rest with
        | inl sameB =>
            exact unary_transport_symm bUnary sameB
        | inr rest =>
            cases rest with
            | inl sameC =>
                exact unary_transport_symm cUnary sameC
            | inr rest =>
                cases rest with
                | inl sameD =>
                    exact unary_transport_symm dUnary sameD
                | inr rest =>
                    cases rest with
                    | inl sameE =>
                        exact unary_transport_symm eUnary sameE
                    | inr rest =>
                        cases rest with
                        | inl sameF =>
                            exact unary_transport_symm fUnary sameF
                        | inr sameG =>
                            exact unary_transport_symm gUnary sameG
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have routedUnary : UnaryHistory routed :=
    unary_cont_closed selectedUnary hUnary selectedRoute
  have blockerUnary : UnaryHistory blockerRead :=
    unary_cont_closed routedUnary pUnary blockerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
              hsame row blockerRead)
          (fun row : BHist =>
            UnaryHistory row ∧
              (hsame row selected ∨ hsame row routed ∨ hsame row blockerRead))
          (fun _row : BHist =>
            Cont selected h routed ∧ Cont routed p blockerRead ∧ hsame p n ∧
              PkgSig bundle p pkg ∧ PkgSig bundle blockerRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro blockerRead
          ⟨packetWitness, hsame_refl blockerRead⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨sourceRow.left, hsame_trans (hsame_symm sameRows) sourceRow.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact
          ⟨unary_transport blockerUnary (hsame_symm sourceRow.right),
            Or.inr (Or.inr sourceRow.right)⟩
      ledger_sound := by
        intro _row _sourceRow
        exact ⟨selectedRoute, blockerRoute, sameProvenanceName, provenancePkg, blockerPkg⟩
    }
  exact ⟨cert, selectedUnary, routedUnary, blockerUnary⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
