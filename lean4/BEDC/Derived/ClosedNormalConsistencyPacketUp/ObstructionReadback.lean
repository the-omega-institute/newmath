import BEDC.Derived.ClosedNormalConsistencyPacketUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedNormalConsistencyPacketUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedNormalConsistencyPacketCarrier_obstruction_readback [AskSetup] [PackageSetup]
    {L T B F K G H C P N positiveRead obstructionRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L ->
      UnaryHistory T ->
        UnaryHistory B ->
          UnaryHistory F ->
            UnaryHistory K ->
              UnaryHistory G ->
                UnaryHistory H ->
                  UnaryHistory C ->
                    UnaryHistory P ->
                      UnaryHistory N ->
                        Cont L T positiveRead ->
                          Cont positiveRead K obstructionRead ->
                            Cont obstructionRead G namedRead ->
                              PkgSig bundle P pkg ->
                                PkgSig bundle N pkg ->
                                  SemanticNameCert
                                      (fun row : BHist => hsame row G ∨ hsame row namedRead)
                                      (fun row : BHist =>
                                        hsame row L ∨ hsame row T ∨ hsame row B ∨
                                          hsame row F ∨ hsame row K ∨ hsame row G ∨
                                            hsame row H ∨ hsame row C ∨ hsame row P ∨
                                              hsame row N ∨ hsame row positiveRead ∨
                                                hsame row obstructionRead ∨
                                                  hsame row namedRead)
                                      (fun row : BHist =>
                                        UnaryHistory row ∧ Cont L T positiveRead ∧
                                          Cont positiveRead K obstructionRead ∧
                                            Cont obstructionRead G namedRead ∧
                                              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                                      hsame ∧
                                    UnaryHistory positiveRead ∧ UnaryHistory obstructionRead ∧
                                      UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig hsame SemanticNameCert UnaryHistory
  intro lUnary tUnary _bUnary _fUnary kUnary gUnary _hUnary _cUnary _pUnary _nUnary
    positiveRoute obstructionRoute namedRoute provenancePkg namePkg
  have positiveUnary : UnaryHistory positiveRead :=
    unary_cont_closed lUnary tUnary positiveRoute
  have obstructionUnary : UnaryHistory obstructionRead :=
    unary_cont_closed positiveUnary kUnary obstructionRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed obstructionUnary gUnary namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row G ∨ hsame row namedRead)
          (fun row : BHist =>
            hsame row L ∨ hsame row T ∨ hsame row B ∨ hsame row F ∨ hsame row K ∨
              hsame row G ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row positiveRead ∨ hsame row obstructionRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L T positiveRead ∧
              Cont positiveRead K obstructionRead ∧ Cont obstructionRead G namedRead ∧
                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := ⟨G, Or.inl (hsame_refl G)⟩
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
        intro row other sameRows source
        cases source with
        | inl sameToG =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameToG)
        | inr sameToNamed =>
            exact Or.inr (hsame_trans (hsame_symm sameRows) sameToNamed)
    }
    pattern_sound := by
      intro _row source
      cases source with
      | inl sameToG =>
          exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl sameToG
      | inr sameToNamed =>
          exact
            Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
              Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr sameToNamed
    ledger_sound := by
      intro row source
      have rowUnary : UnaryHistory row := by
        cases source with
        | inl sameToG =>
            exact unary_transport gUnary (hsame_symm sameToG)
        | inr sameToNamed =>
            exact unary_transport namedUnary (hsame_symm sameToNamed)
      exact
        ⟨rowUnary, positiveRoute, obstructionRoute, namedRoute, provenancePkg, namePkg⟩
  }
  exact ⟨cert, positiveUnary, obstructionUnary, namedUnary⟩

end BEDC.Derived.ClosedNormalConsistencyPacketUp
