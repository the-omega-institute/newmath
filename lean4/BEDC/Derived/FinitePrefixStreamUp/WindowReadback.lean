import BEDC.Derived.FinitePrefixStreamUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.FinitePrefixStreamUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FinitePrefixStreamCarrier_window_readback [AskSetup] [PackageSetup]
    {depth window dyadic regular transport replay provenance localName prefixRead regularRead
      structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory depth →
      UnaryHistory window →
        UnaryHistory dyadic →
          UnaryHistory regular →
            UnaryHistory transport →
              UnaryHistory replay →
                Cont depth window prefixRead →
                  Cont prefixRead dyadic regularRead →
                    Cont transport replay structuralRead →
                      PkgSig bundle provenance pkg →
                        PkgSig bundle localName pkg →
                          UnaryHistory prefixRead ∧ UnaryHistory regularRead ∧
                            UnaryHistory structuralRead ∧ Cont depth window prefixRead ∧
                              Cont prefixRead dyadic regularRead ∧
                                Cont transport replay structuralRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro depthUnary windowUnary dyadicUnary _regularUnary transportUnary replayUnary
    depthWindowPrefixRead prefixReadDyadicRegularRead transportReplayStructuralRead
    provenancePkg localNamePkg
  have prefixReadUnary : UnaryHistory prefixRead :=
    unary_cont_closed depthUnary windowUnary depthWindowPrefixRead
  have regularReadUnary : UnaryHistory regularRead :=
    unary_cont_closed prefixReadUnary dyadicUnary prefixReadDyadicRegularRead
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed transportUnary replayUnary transportReplayStructuralRead
  exact
    ⟨prefixReadUnary, regularReadUnary, structuralReadUnary, depthWindowPrefixRead,
      prefixReadDyadicRegularRead, transportReplayStructuralRead, provenancePkg, localNamePkg⟩

end BEDC.Derived.FinitePrefixStreamUp
