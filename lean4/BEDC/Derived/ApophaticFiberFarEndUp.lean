import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ApophaticFiberFarEndUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem ApophaticFiberFarEndCarrier_noninternality
    {socket fiber ledger boundary inscription transport route provenance name boundaryRead :
      BHist} :
    Cont socket fiber ledger ->
      Cont ledger boundary inscription ->
        Cont inscription route boundaryRead ->
          hsame boundary boundaryRead ->
            SemanticNameCert
              (fun row : BHist => hsame row boundary ∧ hsame row boundaryRead)
              (fun row : BHist =>
                hsame row socket ∨ hsame row fiber ∨ hsame row ledger ∨
                  hsame row boundary ∨ hsame row inscription ∨ hsame row transport ∨
                    hsame row route ∨ hsame row provenance ∨ hsame row name)
              (fun row : BHist =>
                (hsame row boundary ∨ hsame row boundaryRead) ∧
                  Cont socket fiber ledger ∧ Cont ledger boundary inscription ∧
                    Cont inscription route boundaryRead)
              hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro socketFiberLedger ledgerBoundaryInscription inscriptionRouteBoundary boundarySameRead
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro boundary ⟨hsame_refl boundary, boundarySameRead⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨Or.inl source.left, socketFiberLedger, ledgerBoundaryInscription,
          inscriptionRouteBoundary⟩
  }

theorem ApophaticFiberFarEndCarrier_ledger_boundary_route
    {socket fiber ledger boundary inscription transport route provenance name publicRead : BHist} :
    Cont socket fiber ledger ->
      Cont ledger boundary inscription ->
        Cont inscription route publicRead ->
          hsame publicRead inscription ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ hsame row inscription)
                (fun row : BHist =>
                  hsame row socket ∨ hsame row fiber ∨ hsame row ledger ∨
                    hsame row boundary ∨ hsame row inscription ∨ hsame row transport ∨
                      hsame row route ∨ hsame row provenance ∨ hsame row name ∨
                        hsame row publicRead)
                (fun row : BHist =>
                  (hsame row publicRead ∨ hsame row inscription) ∧
                    Cont socket fiber ledger ∧ Cont ledger boundary inscription ∧
                      Cont inscription route publicRead)
                hsame ∧
              hsame publicRead inscription := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro socketFiberLedger ledgerBoundaryInscription inscriptionRoutePublic publicSameInscription
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead ⟨hsame_refl publicRead, publicSameInscription⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.right))))
      ledger_sound := by
        intro _row source
        exact
          ⟨Or.inl source.left, socketFiberLedger, ledgerBoundaryInscription,
            inscriptionRoutePublic⟩
    }
  · exact publicSameInscription

theorem ApophaticFiberFarEnd_scoped_kernel_route
    {socket fiber ledger boundary inscription transport route provenance name read : BHist} :
    Cont socket fiber ledger ->
      Cont ledger boundary inscription ->
        Cont inscription route read ->
          hsame read boundary ->
            SemanticNameCert
                (fun row : BHist => hsame row read ∧ hsame row boundary)
                (fun row : BHist =>
                  hsame row socket ∨ hsame row fiber ∨ hsame row ledger ∨
                    hsame row boundary ∨ hsame row inscription ∨ hsame row transport ∨
                      hsame row route ∨ hsame row provenance ∨ hsame row name)
                (fun row : BHist =>
                  (hsame row read ∨ hsame row boundary) ∧
                    Cont socket fiber ledger ∧ Cont ledger boundary inscription ∧
                      Cont inscription route read)
                hsame ∧
              hsame read boundary := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro socketFiberLedger ledgerBoundaryInscription inscriptionRouteRead readSameBoundary
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro read ⟨hsame_refl read, readSameBoundary⟩
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
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr (Or.inl source.right)))
      ledger_sound := by
        intro _row source
        exact
          ⟨Or.inl source.left, socketFiberLedger, ledgerBoundaryInscription,
            inscriptionRouteRead⟩
    }
  · exact readSameBoundary

theorem ApophaticFiberFarEndCarrier_boundary_bypass_invalid
    {socket fiber ledger boundary bypass : BHist} :
    Cont socket fiber ledger ->
      Cont ledger boundary bypass ->
        hsame bypass (BHist.e0 boundary) -> hsame bypass BHist.Empty -> False := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  intro _socketFiberLedger _ledgerBoundaryBypass bypassBoundary bypassEmpty
  have boundaryEmpty : hsame (BHist.e0 boundary) BHist.Empty :=
    hsame_trans (hsame_symm bypassBoundary) bypassEmpty
  cases boundaryEmpty

theorem ApophaticFiberFarEndCarrier_admission
    {socket fiber ledger boundary inscription transport route provenance name : BHist} :
    Cont socket fiber ledger ->
      Cont ledger boundary inscription ->
        SemanticNameCert
          (fun row : BHist =>
            hsame row socket ∨ hsame row fiber ∨ hsame row ledger ∨
              hsame row boundary ∨ hsame row inscription ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            hsame row socket ∨ hsame row fiber ∨ hsame row ledger ∨
              hsame row boundary ∨ hsame row inscription ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row name)
          (fun row : BHist =>
            (hsame row socket ∨ hsame row fiber ∨ hsame row ledger ∨
              hsame row boundary ∨ hsame row inscription ∨ hsame row transport ∨
                hsame row route ∨ hsame row provenance ∨ hsame row name) ∧
              Cont socket fiber ledger ∧ Cont ledger boundary inscription)
          hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro socketFiberLedger ledgerBoundaryInscription
  exact {
    core := {
      carrier_inhabited := Exists.intro socket (Or.inl (hsame_refl socket))
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
        | inl sameSocket =>
            exact Or.inl (hsame_trans (hsame_symm sameRows) sameSocket)
        | inr rest =>
            cases rest with
            | inl sameFiber =>
                exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameFiber))
            | inr rest =>
                cases rest with
                | inl sameLedger =>
                    exact
                      Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameLedger)))
                | inr rest =>
                    cases rest with
                    | inl sameBoundary =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameBoundary))))
                    | inr rest =>
                        cases rest with
                        | inl sameInscription =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows)
                                          sameInscription)))))
                        | inr rest =>
                            cases rest with
                            | inl sameTransport =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameTransport))))))
                            | inr rest =>
                                cases rest with
                                | inl sameRoute =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl
                                                    (hsame_trans (hsame_symm sameRows)
                                                      sameRoute)))))))
                                | inr rest =>
                                    cases rest with
                                    | inl sameProvenance =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inl
                                                          (hsame_trans (hsame_symm sameRows)
                                                            sameProvenance))))))))
                                    | inr sameName =>
                                        exact
                                          Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr
                                                          (hsame_trans (hsame_symm sameRows)
                                                            sameName))))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact ⟨source, socketFiberLedger, ledgerBoundaryInscription⟩
  }

end BEDC.Derived.ApophaticFiberFarEndUp
