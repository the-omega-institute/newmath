import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyModulusArithmeticUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyModulusArithmeticCarrier [AskSetup] [PackageSetup]
    (S0 S1 mu0 mu1 muMeet sum product dyadic window readback realSeal transport
      replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory S0 ∧
    UnaryHistory S1 ∧
      UnaryHistory mu0 ∧
        UnaryHistory mu1 ∧
          UnaryHistory muMeet ∧
            UnaryHistory dyadic ∧
              UnaryHistory window ∧
                UnaryHistory readback ∧
                  UnaryHistory transport ∧
                    Cont S0 mu0 sum ∧
                      Cont S1 mu1 product ∧
                        Cont muMeet dyadic window ∧
                          Cont window readback realSeal ∧
                            Cont transport provenance localName ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle localName pkg

theorem CauchyModulusArithmeticCarrier_namecert_obligation_carrier
    [AskSetup] [PackageSetup]
    {S0 S1 mu0 mu1 muMeet sum product dyadic window readback realSeal transport
      replay provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusArithmeticCarrier S0 S1 mu0 mu1 muMeet sum product dyadic window
        readback realSeal transport replay provenance localName bundle pkg →
      UnaryHistory S0 ∧ UnaryHistory S1 ∧ UnaryHistory mu0 ∧
        UnaryHistory mu1 ∧ UnaryHistory muMeet ∧ UnaryHistory sum ∧
          UnaryHistory product ∧ UnaryHistory dyadic ∧ UnaryHistory window ∧
            UnaryHistory readback ∧ UnaryHistory realSeal ∧ Cont S0 mu0 sum ∧
              Cont S1 mu1 product ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig UnaryHistory
  intro carrier
  have unaryS0 : UnaryHistory S0 := carrier.left
  have unaryS1 : UnaryHistory S1 := carrier.right.left
  have unaryMu0 : UnaryHistory mu0 := carrier.right.right.left
  have unaryMu1 : UnaryHistory mu1 := carrier.right.right.right.left
  have unaryMuMeet : UnaryHistory muMeet := carrier.right.right.right.right.left
  have unaryDyadic : UnaryHistory dyadic := carrier.right.right.right.right.right.left
  have unaryWindow : UnaryHistory window :=
    carrier.right.right.right.right.right.right.left
  have unaryReadback : UnaryHistory readback :=
    carrier.right.right.right.right.right.right.right.left
  have contSum : Cont S0 mu0 sum :=
    carrier.right.right.right.right.right.right.right.right.right.left
  have contProduct : Cont S1 mu1 product :=
    carrier.right.right.right.right.right.right.right.right.right.right.left
  have contSeal : Cont window readback realSeal :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.left
  have pkgLocalName : PkgSig bundle localName pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right.right.right.right.right
  have unarySum : UnaryHistory sum := unary_cont_closed unaryS0 unaryMu0 contSum
  have unaryProduct : UnaryHistory product := unary_cont_closed unaryS1 unaryMu1 contProduct
  have unaryRealSeal : UnaryHistory realSeal :=
    unary_cont_closed unaryWindow unaryReadback contSeal
  exact
    ⟨unaryS0, unaryS1, unaryMu0, unaryMu1, unaryMuMeet, unarySum, unaryProduct,
      unaryDyadic, unaryWindow, unaryReadback, unaryRealSeal, contSum, contProduct,
      pkgLocalName⟩

end BEDC.Derived.CauchyModulusArithmeticUp
