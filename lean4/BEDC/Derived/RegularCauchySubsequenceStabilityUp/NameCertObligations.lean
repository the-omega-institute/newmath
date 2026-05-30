import BEDC.Derived.RegularCauchySubsequenceStabilityUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchySubsequenceStabilityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem RegularCauchySubsequenceStabilityCarrier_namecert_obligations
    {S T W D R E H C P N replay : BHist} :
    Cont H C replay →
      regularCauchySubsequenceStabilityFields
          (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N) =
        [S, T, W, D, R, E, H, C, P, N] ∧
      S ∈ regularCauchySubsequenceStabilityFields
        (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N) ∧
      T ∈ regularCauchySubsequenceStabilityFields
        (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N) ∧
      W ∈ regularCauchySubsequenceStabilityFields
        (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N) ∧
      D ∈ regularCauchySubsequenceStabilityFields
        (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N) ∧
      R ∈ regularCauchySubsequenceStabilityFields
        (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N) ∧
      E ∈ regularCauchySubsequenceStabilityFields
        (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N) ∧
      SemanticNameCert
        (fun row : BHist =>
          hsame row E ∧
            row ∈ regularCauchySubsequenceStabilityFields
              (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N))
        (fun row : BHist =>
          row ∈ regularCauchySubsequenceStabilityFields
            (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N))
        (fun row : BHist =>
          hsame row E ∧
            row ∈ regularCauchySubsequenceStabilityFields
              (RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N))
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro _replayRoute
  let packet := RegularCauchySubsequenceStabilityUp.mk S T W D R E H C P N
  have fieldsEq :
      regularCauchySubsequenceStabilityFields packet =
        [S, T, W, D, R, E, H, C, P, N] := by
    rfl
  have memS : S ∈ regularCauchySubsequenceStabilityFields packet := by
    exact List.Mem.head _
  have memT : T ∈ regularCauchySubsequenceStabilityFields packet := by
    exact List.Mem.tail _ (List.Mem.head _)
  have memW : W ∈ regularCauchySubsequenceStabilityFields packet := by
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  have memD : D ∈ regularCauchySubsequenceStabilityFields packet := by
    exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  have memR : R ∈ regularCauchySubsequenceStabilityFields packet := by
    exact
      List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
  have memE : E ∈ regularCauchySubsequenceStabilityFields packet := by
    exact
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row E ∧ row ∈ regularCauchySubsequenceStabilityFields packet)
        (fun row : BHist => row ∈ regularCauchySubsequenceStabilityFields packet)
        (fun row : BHist =>
          hsame row E ∧ row ∈ regularCauchySubsequenceStabilityFields packet)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro E ⟨hsame_refl E, memE⟩
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
          cases sameRows
          exact source
      }
      pattern_sound := by
        intro _row source
        exact source.right
      ledger_sound := by
        intro _row source
        exact source
    }
  exact ⟨fieldsEq, memS, memT, memW, memD, memR, memE, cert⟩

end BEDC.Derived.RegularCauchySubsequenceStabilityUp
