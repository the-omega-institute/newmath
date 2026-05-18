import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_source_lock [AskSetup] [PackageSetup]
    {a b c d e f g h p n source routed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      (hsame source a ∨ hsame source b ∨ hsame source c ∨ hsame source d ∨
        hsame source e ∨ hsame source f ∨ hsame source g) →
        Cont source h routed →
          PkgSig bundle routed pkg →
            SemanticNameCert
                  (fun row : BHist =>
                    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
                      hsame row routed)
                  (fun row : BHist => UnaryHistory source ∧ Cont source h row)
                  (fun _row : BHist =>
                    hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle routed pkg)
                  hsame ∧
                UnaryHistory source ∧ UnaryHistory routed := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet sourceRow sourceRouteRouted routedPkg
  have packetWitness := packet
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, _routeCD,
      _routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have sourceUnary : UnaryHistory source := by
    cases sourceRow with
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
    unary_cont_closed sourceUnary hUnary sourceRouteRouted
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
              hsame row routed)
          (fun row : BHist => UnaryHistory source ∧ Cont source h row)
          (fun _row : BHist =>
            hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle routed pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro routed ⟨packetWitness, hsame_refl routed⟩
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
          intro _row _other sameRows sourcePacket
          exact
            ⟨sourcePacket.left, hsame_trans (hsame_symm sameRows) sourcePacket.right⟩
      }
      pattern_sound := by
        intro row sourcePacket
        exact
          ⟨sourceUnary,
            cont_result_hsame_transport sourceRouteRouted (hsame_symm sourcePacket.right)⟩
      ledger_sound := by
        intro _row _sourcePacket
        exact ⟨sameProvenanceName, provenancePkg, routedPkg⟩
    }
  exact ⟨cert, sourceUnary, routedUnary⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
