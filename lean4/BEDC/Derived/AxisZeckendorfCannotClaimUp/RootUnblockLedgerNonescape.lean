import BEDC.Derived.AxisZeckendorfCannotClaimUp

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxisZeckendorfCannotClaimRegistryPacket_root_unblock_ledger_nonescape
    [AskSetup] [PackageSetup] {a b c d e f g h p n rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      Cont h p rootRead ->
        PkgSig bundle rootRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row rootRead /\ UnaryHistory row)
              (fun row : BHist =>
                hsame row h \/ hsame row p \/ hsame row n \/ hsame row rootRead)
              (fun _row : BHist =>
                Cont a b h /\ Cont c d h /\ Cont e f h /\ Cont h p rootRead /\
                  hsame p n /\ PkgSig bundle p pkg /\ PkgSig bundle rootRead pkg)
              hsame /\
            UnaryHistory h /\ UnaryHistory p /\ UnaryHistory rootRead /\
              hsame p n := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro packet rootRoute rootPkg
  obtain
    ⟨aUnary, bUnary, _cUnary, _dUnary, _eUnary, _fUnary, _gUnary, routeAB, routeCD,
      routeEF, pUnary, sameProvenanceName, provenancePkg⟩ := packet
  have hUnary : UnaryHistory h :=
    unary_cont_closed aUnary bUnary routeAB
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed hUnary pUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootRead /\ UnaryHistory row)
          (fun row : BHist =>
            hsame row h \/ hsame row p \/ hsame row n \/ hsame row rootRead)
          (fun _row : BHist =>
            Cont a b h /\ Cont c d h /\ Cont e f h /\ Cont h p rootRead /\
              hsame p n /\ PkgSig bundle p pkg /\ PkgSig bundle rootRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
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
          intro _row _other same source
          cases same
          exact source
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row _source
        exact
          ⟨routeAB, routeCD, routeEF, rootRoute, sameProvenanceName, provenancePkg,
            rootPkg⟩
    }
  exact ⟨cert, hUnary, pUnary, rootUnary, sameProvenanceName⟩

end BEDC.Derived.AxisZeckendorfCannotClaimUp
