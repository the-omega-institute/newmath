import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyCompletionUnitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyCompletionUnitCarrier [AskSetup] [PackageSetup]
    (source window tolerance readback sealRow completion transport route provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory window ∧ UnaryHistory tolerance ∧
    UnaryHistory readback ∧ UnaryHistory sealRow ∧ UnaryHistory completion ∧
      UnaryHistory transport ∧ UnaryHistory route ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont source window tolerance ∧ Cont tolerance readback sealRow ∧
          Cont sealRow route completion ∧ hsame transport BHist.Empty ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg

theorem CauchyCompletionUnitNameCert_obligations [AskSetup] [PackageSetup]
    {source window tolerance readback sealRow completion transport route provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport route
        provenance name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport
            route provenance name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport
            route provenance name bundle pkg ∧ hsame row completion)
        (fun row : BHist =>
          CauchyCompletionUnitCarrier source window tolerance readback sealRow completion transport
            route provenance name bundle pkg ∧ hsame row completion)
        hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro completion ⟨carrier, hsame_refl completion⟩
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
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CauchyCompletionUnitUp
