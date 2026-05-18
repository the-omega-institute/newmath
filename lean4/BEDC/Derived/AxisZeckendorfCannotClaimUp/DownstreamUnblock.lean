import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_downstream_unblock [AskSetup] [PackageSetup]
    {a b c d e f g h p n downstream : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg →
      Cont h p downstream →
        PkgSig bundle downstream pkg →
          SemanticNameCert
            (fun row : BHist =>
              hsame row downstream ∧ UnaryHistory row ∧ PkgSig bundle downstream pkg)
            (fun row : BHist => Cont h p downstream ∧ hsame row downstream)
            (fun _row : BHist =>
              AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
                PkgSig bundle p pkg ∧ PkgSig bundle downstream pkg ∧ hsame p n)
            hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro packet downstreamRoute downstreamPkg
  have packetWitness :
      AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg := packet
  obtain
    ⟨aUnary, bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, routeAB, _routeCD,
      _routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have downstreamUnary : UnaryHistory downstream :=
    unary_cont_closed hUnary pUnary downstreamRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro downstream ⟨hsame_refl downstream, downstreamUnary, downstreamPkg⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right.left sameRows, source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨downstreamRoute, source.left⟩
    ledger_sound := by
      intro _row _source
      exact ⟨packetWitness, provenancePkg, downstreamPkg, sameProvenanceName⟩
  }

end BEDC.Derived.AxisZeckendorfCannotClaimUp
