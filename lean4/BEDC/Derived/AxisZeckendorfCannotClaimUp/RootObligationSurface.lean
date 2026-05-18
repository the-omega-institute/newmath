import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_root_obligation_surface [AskSetup]
    [PackageSetup] {a b c d e f g h p n selected routed audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      (hsame selected a ∨ hsame selected b ∨ hsame selected c ∨ hsame selected d ∨
        hsame selected e ∨ hsame selected f ∨ hsame selected g) ->
        Cont selected h routed ->
          Cont routed p audit ->
            PkgSig bundle audit pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row selected ∧ UnaryHistory row)
                  (fun row : BHist =>
                    Cont selected h routed ∧ Cont routed p audit ∧ hsame row selected)
                  (fun _row : BHist =>
                    hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle audit pkg)
                  hsame ∧
                UnaryHistory selected ∧ UnaryHistory routed ∧ UnaryHistory audit ∧
                  Cont selected h routed ∧ Cont routed p audit ∧ hsame p n ∧
                    PkgSig bundle p pkg ∧ PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg SemanticNameCert hsame
  intro packet selectedRow selectedRoute routedAudit auditPkg
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, _routeAB, _routeCD,
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
  have routedUnary : UnaryHistory routed :=
    unary_cont_closed selectedUnary
      (unary_cont_closed aUnary bUnary
        (show Cont a b h from by
          exact _routeAB))
      selectedRoute
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed routedUnary pUnary routedAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row selected ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont selected h routed ∧ Cont routed p audit ∧ hsame row selected)
          (fun _row : BHist =>
            hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle audit pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro selected
          ⟨hsame_refl selected, selectedUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row other same source
          have sameOtherSelected : hsame other selected :=
            hsame_trans (hsame_symm same) source.left
          exact ⟨sameOtherSelected, unary_transport source.right same⟩
      }
      pattern_sound := by
        intro row source
        exact ⟨selectedRoute, routedAudit, source.left⟩
      ledger_sound := by
        intro _row _source
        exact ⟨sameProvenanceName, provenancePkg, auditPkg⟩
    }
  exact
    ⟨cert, selectedUnary, routedUnary, auditUnary, selectedRoute, routedAudit,
      sameProvenanceName, provenancePkg, auditPkg⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
