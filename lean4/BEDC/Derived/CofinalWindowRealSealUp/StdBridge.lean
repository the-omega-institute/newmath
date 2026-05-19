import BEDC.Derived.CofinalWindowRealSealUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CofinalWindowRealSealUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow

theorem CofinalWindowRealSealUp_StdBridge [AskSetup] [PackageSetup] {flow : EventFlow}
    {B T W D R E X G H C P N bridgeRead : BHist} {bundle : ProbeBundle ProbeName}
    {pkg : Pkg} :
    cofinalWindowRealSealFromEventFlow flow =
        some (CofinalWindowRealSealUp.mk B T W D R E X G H C P N) ->
      Cont E G bridgeRead ->
        PkgSig bundle N pkg ->
          PkgSig bundle bridgeRead pkg ->
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
              SemanticNameCert
                (fun row : BHist =>
                  hsame row bridgeRead ∧
                    ∃ packet : CofinalWindowRealSealUp,
                      packet = CofinalWindowRealSealUp.mk B T W D R E X G H C P N)
                (fun row : BHist => Cont E G row)
                (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
                hsame ∧
                PkgSig bundle N pkg ∧ PkgSig bundle bridgeRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro hflow bridgeRoute namePkg bridgePkg
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
  have sourceBridge :
      (fun row : BHist =>
        hsame row bridgeRead ∧
          ∃ packet : CofinalWindowRealSealUp,
            packet = CofinalWindowRealSealUp.mk B T W D R E X G H C P N) bridgeRead := by
    exact ⟨hsame_refl bridgeRead,
      ⟨CofinalWindowRealSealUp.mk B T W D R E X G H C P N, rfl⟩⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row bridgeRead ∧
            ∃ packet : CofinalWindowRealSealUp,
              packet = CofinalWindowRealSealUp.mk B T W D R E X G H C P N)
        (fun row : BHist => Cont E G row)
        (fun row : BHist => hsame row bridgeRead ∧ PkgSig bundle bridgeRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro bridgeRead sourceBridge
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact cont_result_hsame_transport bridgeRoute (hsame_symm source.left)
      ledger_sound := by
        intro _row source
        exact ⟨source.left, bridgePkg⟩
    }
  exact ⟨sourceRoute, cert, namePkg, bridgePkg⟩

end BEDC.Derived.CofinalWindowRealSealUp
