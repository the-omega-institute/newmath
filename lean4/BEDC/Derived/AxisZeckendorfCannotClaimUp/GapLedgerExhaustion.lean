import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_gap_ledger_exhaustion
    [AskSetup] [PackageSetup] {a b c d e f g h p n gapRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      Cont h p gapRead ->
        PkgSig bundle gapRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row h ∨ hsame row p ∨ hsame row n ∨ hsame row gapRead)
              (fun _row : BHist =>
                Cont a b h ∧ Cont c d h ∧ Cont e f h ∧ Cont h p gapRead ∧
                  hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle gapRead pkg)
              hsame ∧
            UnaryHistory h ∧ UnaryHistory p ∧ UnaryHistory gapRead ∧ hsame p n := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet gapRoute gapPkg
  obtain
    ⟨aUnary, bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, routeAB, routeCD,
      routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed hUnary pUnary gapRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row gapRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row h ∨ hsame row p ∨ hsame row n ∨ hsame row gapRead)
          (fun _row : BHist =>
            Cont a b h ∧ Cont c d h ∧ Cont e f h ∧ Cont h p gapRead ∧
              hsame p n ∧ PkgSig bundle p pkg ∧ PkgSig bundle gapRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro gapRead ⟨hsame_refl gapRead, gapReadUnary⟩
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
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              unary_transport sourceRow.right sameRows⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr sourceRow.left))
      ledger_sound := by
        intro _row _sourceRow
        exact
          ⟨routeAB, routeCD, routeEF, gapRoute, sameProvenanceName, provenancePkg, gapPkg⟩
    }
  exact ⟨cert, hUnary, pUnary, gapReadUnary, sameProvenanceName⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
