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

def CauchyConvolutionPacket [AskSetup] [PackageSetup]
    (leftSeries rightSeries convolution prefixRow tailBudget handoff sealRow transports routes
      provenance nameCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory leftSeries ∧ UnaryHistory rightSeries ∧ UnaryHistory convolution ∧
    UnaryHistory prefixRow ∧ UnaryHistory tailBudget ∧ UnaryHistory handoff ∧
      UnaryHistory sealRow ∧
      UnaryHistory transports ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory nameCert ∧ Cont leftSeries rightSeries convolution ∧
          Cont convolution prefixRow tailBudget ∧ Cont tailBudget handoff sealRow ∧
            PkgSig bundle sealRow pkg

theorem CauchyConvolutionPacket_semantic_name_certificate [AskSetup] [PackageSetup]
    {leftSeries rightSeries convolution prefixRow tailBudget handoff sealRow transports routes
      provenance nameCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvolutionPacket leftSeries rightSeries convolution prefixRow tailBudget handoff sealRow
        transports routes provenance nameCert bundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          CauchyConvolutionPacket leftSeries rightSeries convolution prefixRow tailBudget handoff
              sealRow transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          CauchyConvolutionPacket leftSeries rightSeries convolution prefixRow tailBudget handoff
              sealRow transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        (fun row : BHist =>
          CauchyConvolutionPacket leftSeries rightSeries convolution prefixRow tailBudget handoff
              sealRow transports routes provenance nameCert bundle pkg ∧ hsame row nameCert)
        hsame := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro nameCert (And.intro packet (hsame_refl nameCert))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact And.intro source.left (hsame_trans (hsame_symm sameRows) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

def CauchyConvolutionCarrierSurface [AskSetup] [PackageSetup]
    (F G K A D R E H C P N endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory F ∧ UnaryHistory G ∧ UnaryHistory K ∧ UnaryHistory A ∧
    UnaryHistory D ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory H ∧
      UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧ UnaryHistory endpoint ∧
        Cont F G K ∧ Cont K A D ∧ Cont D R E ∧ Cont E N endpoint ∧
          PkgSig bundle endpoint pkg

theorem CauchyConvolutionTailBudgetCompatibility [AskSetup] [PackageSetup]
    {F G K A D R E H C P N endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyConvolutionCarrierSurface F G K A D R E H C P N endpoint bundle pkg ->
      UnaryHistory F ∧ UnaryHistory G ∧ UnaryHistory K ∧ UnaryHistory A ∧
        UnaryHistory D ∧ UnaryHistory R ∧ Cont F G K ∧ Cont K A D ∧
          Cont D R E ∧ Cont E N endpoint ∧ PkgSig bundle endpoint pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont
  intro carrier
  obtain ⟨fUnary, gUnary, kUnary, aUnary, dUnary, rUnary, _eUnary, _hUnary,
    _cUnary, _pUnary, _nUnary, _endpointUnary, sourceConvolution, convolutionBudget,
    budgetHandoff, sealEndpoint, pkgSig⟩ := carrier
  exact
    ⟨fUnary, gUnary, kUnary, aUnary, dUnary, rUnary, sourceConvolution,
      convolutionBudget, budgetHandoff, sealEndpoint, pkgSig⟩

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
