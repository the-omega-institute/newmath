import BEDC.Derived.RealCompletionExactBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealCompletionExactBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealCompletionExactBoundaryCofinalTerminalDeterminacy [AskSetup] [PackageSetup]
    {L K J S W R D E E' H C P N budgetRead terminalRead terminalRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W ->
      UnaryHistory R ->
        UnaryHistory E ->
          UnaryHistory E' ->
            Cont W R budgetRead ->
              Cont budgetRead E terminalRead ->
                Cont budgetRead E' terminalRead' ->
                  PkgSig bundle terminalRead pkg ->
                    PkgSig bundle terminalRead' pkg ->
                      hsame E E' ->
                        realCompletionExactBoundaryFields
                            (RealCompletionExactBoundaryUp.mk L K J S W R D E H C P N) =
                          [L, K, J, S, W, R, D, E, H, C, P, N] ∧
                          hsame terminalRead terminalRead' ∧ PkgSig bundle terminalRead pkg ∧
                            PkgSig bundle terminalRead' pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro _unaryW _unaryR _unaryE _unaryE' _budgetRoute terminalRoute terminalRoute'
    terminalPkg terminalPkg' sameTerminalFace
  have sameTerminalRead : hsame terminalRead terminalRead' :=
    cont_respects_hsame (hsame_refl budgetRead) sameTerminalFace terminalRoute terminalRoute'
  exact ⟨rfl, sameTerminalRead, terminalPkg, terminalPkg'⟩

end BEDC.Derived.RealCompletionExactBoundaryUp
