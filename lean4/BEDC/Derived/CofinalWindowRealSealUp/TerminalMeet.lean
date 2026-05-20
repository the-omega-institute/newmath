import BEDC.Derived.CofinalWindowRealSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package

namespace BEDC.Derived.CofinalWindowRealSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow

theorem CofinalWindowRealSeal_terminal_meet [AskSetup] [PackageSetup] {flow : EventFlow}
    {B T W D R E X G H C P N terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cofinalWindowRealSealFromEventFlow flow =
        some (CofinalWindowRealSealUp.mk B T W D R E X G H C P N) ->
      Cont X G terminal ->
        PkgSig bundle terminal pkg ->
          (∃ (eB eT eW eD eR eE eX eG : List BMark) (tail : EventFlow),
            flow = eB :: eT :: eW :: eD :: eR :: eE :: eX :: eG :: tail ∧
              cofinalWindowRealSealDecodeBHist eB = B ∧
                cofinalWindowRealSealDecodeBHist eT = T ∧
                  cofinalWindowRealSealDecodeBHist eW = W ∧
                    cofinalWindowRealSealDecodeBHist eD = D ∧
                      cofinalWindowRealSealDecodeBHist eR = R ∧
                        cofinalWindowRealSealDecodeBHist eE = E ∧
                          cofinalWindowRealSealDecodeBHist eX = X ∧
                            cofinalWindowRealSealDecodeBHist eG = G) ∧
            Cont X G terminal ∧ PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist BMark ProbeBundle PkgSig Cont EventFlow
  intro hflow terminalRoute terminalPkg
  have sourceRoute :
      ∃ (eB eT eW eD eR eE eX eG : List BMark) (tail : EventFlow),
        flow = eB :: eT :: eW :: eD :: eR :: eE :: eX :: eG :: tail ∧
          cofinalWindowRealSealDecodeBHist eB = B ∧
            cofinalWindowRealSealDecodeBHist eT = T ∧
              cofinalWindowRealSealDecodeBHist eW = W ∧
                cofinalWindowRealSealDecodeBHist eD = D ∧
                  cofinalWindowRealSealDecodeBHist eR = R ∧
                    cofinalWindowRealSealDecodeBHist eE = E ∧
                      cofinalWindowRealSealDecodeBHist eX = X ∧
                        cofinalWindowRealSealDecodeBHist eG = G :=
    CofinalWindowRealSeal_source_exhaustion hflow
  exact ⟨sourceRoute, terminalRoute, terminalPkg⟩

end BEDC.Derived.CofinalWindowRealSealUp
