import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyConvolutionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyConvolutionCarrier [AskSetup] [PackageSetup]
    (sourceLeft sourceRight convolutionLedger productPrefix dyadicTail regSeqHandoff realSeal
      transport route name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceLeft ∧ UnaryHistory sourceRight ∧ UnaryHistory convolutionLedger ∧
    UnaryHistory productPrefix ∧ UnaryHistory dyadicTail ∧ UnaryHistory regSeqHandoff ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory route ∧
        UnaryHistory name ∧ Cont sourceLeft sourceRight convolutionLedger ∧
          Cont convolutionLedger productPrefix dyadicTail ∧
            Cont dyadicTail regSeqHandoff realSeal ∧ Cont realSeal transport route ∧
              PkgSig bundle route pkg ∧ PkgSig bundle name pkg

theorem CauchyConvolutionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {sourceLeft sourceRight convolutionLedger productPrefix dyadicTail regSeqHandoff realSeal
      transport route name : BHist} :
    CauchyConvolutionCarrier sourceLeft sourceRight convolutionLedger productPrefix dyadicTail
        regSeqHandoff realSeal transport route name bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyConvolutionCarrier sourceLeft sourceRight convolutionLedger productPrefix
            dyadicTail regSeqHandoff realSeal transport route name bundle pkg ∧
              hsame row realSeal)
        (fun row : BHist =>
          CauchyConvolutionCarrier sourceLeft sourceRight convolutionLedger productPrefix
            dyadicTail regSeqHandoff realSeal transport route name bundle pkg ∧
              hsame row realSeal)
        (fun row : BHist =>
          CauchyConvolutionCarrier sourceLeft sourceRight convolutionLedger productPrefix
            dyadicTail regSeqHandoff realSeal transport route name bundle pkg ∧
              hsame row realSeal)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro realSeal (And.intro carrier (hsame_refl realSeal))
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
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.CauchyConvolutionUp
