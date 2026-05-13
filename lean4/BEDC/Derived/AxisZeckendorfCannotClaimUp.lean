import BEDC.Derived.AxisZeckendorf
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxisZeckendorfCannotClaimUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def AxisZeckendorfCannotClaimRegistryPacket [AskSetup] [PackageSetup]
    (a b c d e f g h p n : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory a ∧
    UnaryHistory b ∧
      UnaryHistory c ∧
        UnaryHistory d ∧
          UnaryHistory e ∧
            UnaryHistory f ∧
              UnaryHistory g ∧
                Cont a b h ∧
                  Cont c d h ∧ Cont e f h ∧ hsame p n ∧ PkgSig bundle p pkg

theorem AxisZeckendorfCannotClaimRegistryPacket_source_row_coverage [AskSetup] [PackageSetup]
    {a b c d e f g h p n : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      UnaryHistory a ∧ UnaryHistory b ∧ UnaryHistory c ∧ UnaryHistory d ∧
        UnaryHistory e ∧ UnaryHistory f ∧ UnaryHistory g ∧ Cont a b h ∧ Cont c d h ∧
          Cont e f h ∧ hsame p n ∧ PkgSig bundle p pkg := by
  intro packet
  obtain
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      sameProvenanceName, pkgSig⟩ := packet
  exact
    ⟨aUnary, bUnary, cUnary, dUnary, eUnary, fUnary, gUnary, routeAB, routeCD, routeEF,
      sameProvenanceName, pkgSig⟩

theorem AxisZeckendorfCannotClaimRegistryPacket_semantic_name_certificate [AskSetup]
    [PackageSetup] {a b c d e f g h p n : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
            hsame row n)
        (fun row : BHist =>
          AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
            hsame row n)
        (fun row : BHist =>
          AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg ∧
            hsame row n)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont PkgSig hsame SemanticNameCert
  intro packet
  have packetWitness :
      AxisZeckendorfCannotClaimRegistryPacket a b c d e f g h p n bundle pkg := packet
  exact {
    core := {
      carrier_inhabited := Exists.intro n ⟨packetWitness, hsame_refl n⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.AxisZeckendorfCannotClaimUp
