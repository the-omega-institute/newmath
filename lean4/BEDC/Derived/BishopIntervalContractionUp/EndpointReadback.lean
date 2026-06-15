import BEDC.Derived.BishopIntervalContractionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BishopIntervalContractionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem BishopIntervalContractionEndpointReadback [AskSetup] [PackageSetup]
    {I F L D W R E H C P N intervalRead windowRead readbackSeal endpointRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont I F intervalRead ->
      Cont D W windowRead ->
        Cont R E readbackSeal ->
          Cont readbackSeal N endpointRead ->
            PkgSig bundle P pkg ->
              PkgSig bundle N pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row endpointRead)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row F ∨ hsame row L ∨ hsame row D ∨
                      hsame row W ∨ hsame row R ∨ hsame row E ∨ hsame row H ∨
                        hsame row C ∨ hsame row P ∨ hsame row N ∨
                          hsame row endpointRead)
                  (fun row : BHist =>
                    Cont I F intervalRead ∧ Cont D W windowRead ∧
                      Cont R E readbackSeal ∧ Cont readbackSeal N endpointRead ∧
                        PkgSig bundle P pkg ∧ PkgSig bundle N pkg ∧
                          hsame row endpointRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig SemanticNameCert hsame
  intro intervalRoute windowRoute readbackRoute endpointRoute provenancePkg localNamePkg
  refine
    { core :=
        { carrier_inhabited := ?carrier_inhabited
          equiv_refl := ?equiv_refl
          equiv_symm := ?equiv_symm
          equiv_trans := ?equiv_trans
          carrier_respects_equiv := ?carrier_respects_equiv }
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · exact ⟨endpointRead, hsame_refl endpointRead⟩
  · intro row _source
    exact hsame_refl row
  · intro _row _other sameRows
    exact hsame_symm sameRows
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other sameRows source
    exact hsame_trans (hsame_symm sameRows) source
  · intro _row source
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr source))))))))))
  · intro _row source
    exact
      ⟨intervalRoute, windowRoute, readbackRoute, endpointRoute, provenancePkg,
        localNamePkg, source⟩

end BEDC.Derived.BishopIntervalContractionUp
