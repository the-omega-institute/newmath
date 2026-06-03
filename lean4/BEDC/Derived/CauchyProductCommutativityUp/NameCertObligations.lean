import BEDC.Derived.CauchyProductCommutativityUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CauchyProductCommutativityUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem CauchyProductCommutativityCarrier_namecert_obligations
    {Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N replay : BHist} :
    Cont H C replay →
      cauchyProductCommutativityFields
          (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N) =
        [Pxy, Pyx, Wx, Wy, Dxy, Dyx, Rxy, Ryx, Exy, Eyx, H, C, Q, N] ∧
      Pxy ∈ cauchyProductCommutativityFields
        (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N) ∧
      Pyx ∈ cauchyProductCommutativityFields
        (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N) ∧
      Exy ∈ cauchyProductCommutativityFields
        (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N) ∧
      Eyx ∈ cauchyProductCommutativityFields
        (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N) ∧
      SemanticNameCert
        (fun row : BHist =>
          hsame row Exy ∧
            row ∈ cauchyProductCommutativityFields
              (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N))
        (fun row : BHist =>
          row ∈ cauchyProductCommutativityFields
            (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N))
        (fun row : BHist =>
          hsame row Exy ∧
            row ∈ cauchyProductCommutativityFields
              (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N))
        hsame ∧
      SemanticNameCert
        (fun row : BHist =>
          hsame row Eyx ∧
            row ∈ cauchyProductCommutativityFields
              (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N))
        (fun row : BHist =>
          row ∈ cauchyProductCommutativityFields
            (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N))
        (fun row : BHist =>
          hsame row Eyx ∧
            row ∈ cauchyProductCommutativityFields
              (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N))
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro _replayRoute
  let packet :=
    CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N
  have fieldsEq :
      cauchyProductCommutativityFields packet =
        [Pxy, Pyx, Wx, Wy, Dxy, Dyx, Rxy, Ryx, Exy, Eyx, H, C, Q, N] := by
    rfl
  have memPxy : Pxy ∈ cauchyProductCommutativityFields packet := by
    exact List.Mem.head _
  have memPyx : Pyx ∈ cauchyProductCommutativityFields packet := by
    exact List.Mem.tail _ (List.Mem.head _)
  have memExy : Exy ∈ cauchyProductCommutativityFields packet := by
    exact
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _ (List.Mem.head _))))))))
  have memEyx : Eyx ∈ cauchyProductCommutativityFields packet := by
    exact
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))
  have certExy :
      SemanticNameCert
        (fun row : BHist => hsame row Exy ∧ row ∈ cauchyProductCommutativityFields packet)
        (fun row : BHist => row ∈ cauchyProductCommutativityFields packet)
        (fun row : BHist => hsame row Exy ∧ row ∈ cauchyProductCommutativityFields packet)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro Exy ⟨hsame_refl Exy, memExy⟩
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
  have certEyx :
      SemanticNameCert
        (fun row : BHist => hsame row Eyx ∧ row ∈ cauchyProductCommutativityFields packet)
        (fun row : BHist => row ∈ cauchyProductCommutativityFields packet)
        (fun row : BHist => hsame row Eyx ∧ row ∈ cauchyProductCommutativityFields packet)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro Eyx ⟨hsame_refl Eyx, memEyx⟩
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
  exact ⟨fieldsEq, memPxy, memPyx, memExy, memEyx, certExy, certEyx⟩

end BEDC.Derived.CauchyProductCommutativityUp
