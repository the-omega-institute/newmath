import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimUp_StdBridge [AskSetup] [PackageSetup]
    {a b c d e f g h p n publicRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      Cont h p publicRead ->
        PkgSig bundle publicRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
                hsame row n)
            (fun row : BHist =>
              hsame row publicRead ∨ hsame row h ∨ hsame row p ∨ hsame row n)
            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle publicRead pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory SemanticNameCert
  intro packet publicRoute publicPkg
  obtain
    ⟨_aUnary, _bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, hUnary,
      pUnary, publicUnary, _publicRoute, sameProvenanceName, _provenancePkg,
      publicPkg'⟩ :=
    AxisZeckendorfCannotClaimRegistryPacket_public_boundary packet publicRoute publicPkg
  have nUnary : UnaryHistory n :=
    unary_transport pUnary sameProvenanceName
  exact {
    core := {
      carrier_inhabited := Exists.intro n ⟨packet, hsame_refl n⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr source.right))
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row :=
        unary_transport_symm nUnary source.right
      exact ⟨rowUnary, publicPkg'⟩
  }

end BEDC.Derived.AxisZeckendorfCannotClaimUp
