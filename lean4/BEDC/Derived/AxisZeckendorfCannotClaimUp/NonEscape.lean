import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem AxisZeckendorfCannotClaimRegistryPacket_non_escape [AskSetup] [PackageSetup]
    {a b c d e f g h p n publicRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      Cont h p publicRead ->
        SemanticNameCert
          (fun row : BHist =>
            AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
              hsame row publicRead)
          (fun row : BHist => Cont h p publicRead ∧ hsame row publicRead)
          (fun row : BHist => PkgSig bundle p pkg ∧ hsame row publicRead)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert
  intro packet publicRoute
  have packetWitness :
      AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg := packet
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, _routeAB,
      _routeCD, _routeEF, _pUnary, _sameProvenanceName, provenancePkg⟩ := packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨packetWitness, hsame_refl publicRead⟩
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
          ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨publicRoute, source.right⟩
    ledger_sound := by
      intro _row source
      exact ⟨provenancePkg, source.right⟩
  }

end BEDC.Derived.AxisZeckendorfCannotClaimUp
