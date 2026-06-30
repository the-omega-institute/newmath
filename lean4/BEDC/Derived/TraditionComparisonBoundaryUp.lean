import BEDC.Derived.TraditionComparisonBoundaryUp.TasteGate

namespace BEDC.Derived.TraditionComparisonBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def TraditionComparisonBoundaryCarrier (S L R D H C P N : BHist) : Prop :=
  hsame H (append L R) ∧ Cont L R D ∧ Cont D H C ∧ hsame P P ∧ hsame N N

theorem TraditionComparisonBoundary_source_registry_obligation
    {S L R D H C P N sourceRead registryRead : BHist} :
    traditionComparisonBoundaryClassifier (TraditionComparisonBoundaryUp.mk S L R D H C P N) ->
      Cont S N sourceRead ->
        Cont sourceRead P registryRead ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row registryRead ∧ Cont S N sourceRead ∧
                  Cont sourceRead P registryRead)
              (fun row : BHist =>
                hsame row S ∨ hsame row N ∨ hsame row registryRead)
              (fun row : BHist =>
                hsame row registryRead ∧ hsame H (append L R) ∧
                  Cont L R D ∧ Cont D H C)
              hsame ∧
            hsame H (append L R) ∧ Cont L R D ∧ Cont D H C ∧
              Cont S N sourceRead ∧ Cont sourceRead P registryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro accepted sourceRoute registryRoute
  obtain ⟨transportSame, distinctionRoute, replayRoute, _provenanceSame, _localSame⟩ :=
    accepted
  have sourceAtRegistry :
      hsame registryRead registryRead ∧ Cont S N sourceRead ∧
        Cont sourceRead P registryRead :=
    ⟨hsame_refl registryRead, sourceRoute, registryRoute⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row registryRead ∧ Cont S N sourceRead ∧ Cont sourceRead P registryRead)
          (fun row : BHist =>
            hsame row S ∨ hsame row N ∨ hsame row registryRead)
          (fun row : BHist =>
            hsame row registryRead ∧ hsame H (append L R) ∧
              Cont L R D ∧ Cont D H C)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro registryRead sourceAtRegistry
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
            source.right.left, source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, transportSame, distinctionRoute, replayRoute⟩
  }
  exact
    ⟨cert, transportSame, distinctionRoute, replayRoute, sourceRoute, registryRoute⟩

theorem TraditionComparisonBoundary_export_consistency_obligation
    {S L R D H C P N exportRead registryRead : BHist} :
    traditionComparisonBoundaryClassifier (TraditionComparisonBoundaryUp.mk S L R D H C P N) ->
      Cont D H exportRead ->
        Cont exportRead C registryRead ->
          SemanticNameCert
              (fun row : BHist =>
                hsame row registryRead ∧ Cont D H exportRead ∧
                  Cont exportRead C registryRead)
              (fun row : BHist =>
                hsame row S ∨ hsame row L ∨ hsame row R ∨ hsame row D ∨
                  hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                    hsame row registryRead)
              (fun row : BHist =>
                hsame row registryRead ∧ hsame H (append L R) ∧
                  Cont L R D ∧ Cont D H C)
              hsame ∧
            hsame H (append L R) ∧ Cont L R D ∧ Cont D H C ∧
              Cont D H exportRead ∧ Cont exportRead C registryRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro accepted exportRoute registryRoute
  obtain ⟨transportSame, distinctionRoute, replayRoute, _provenanceSame, _localSame⟩ :=
    accepted
  have sourceAtRegistry :
      hsame registryRead registryRead ∧ Cont D H exportRead ∧
        Cont exportRead C registryRead :=
    ⟨hsame_refl registryRead, exportRoute, registryRoute⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row registryRead ∧ Cont D H exportRead ∧ Cont exportRead C registryRead)
          (fun row : BHist =>
            hsame row S ∨ hsame row L ∨ hsame row R ∨ hsame row D ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row registryRead)
          (fun row : BHist =>
            hsame row registryRead ∧ hsame H (append L R) ∧
              Cont L R D ∧ Cont D H C)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro registryRead sourceAtRegistry
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
            source.right.left, source.right.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, transportSame, distinctionRoute, replayRoute⟩
  }
  exact ⟨cert, transportSame, distinctionRoute, replayRoute, exportRoute, registryRoute⟩

theorem TraditionComparisonBoundary_scoped_kernel_route {S L R D H C P N routeRead : BHist} :
    traditionComparisonBoundaryClassifier (TraditionComparisonBoundaryUp.mk S L R D H C P N) ->
      Cont C N routeRead ->
        SemanticNameCert
            (fun row : BHist => hsame row routeRead ∧ Cont C N routeRead)
            (fun row : BHist =>
              hsame row S ∨ hsame row L ∨ hsame row R ∨ hsame row D ∨
                hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                  hsame row routeRead)
            (fun row : BHist =>
              hsame row routeRead ∧ hsame H (append L R) ∧ Cont L R D ∧
                Cont D H C ∧ Cont C N routeRead)
            hsame ∧
          hsame H (append L R) ∧ Cont L R D ∧ Cont D H C ∧ Cont C N routeRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert append
  intro accepted routeRoute
  obtain ⟨transportSame, distinctionRoute, replayRoute, _provenanceSame, _localSame⟩ :=
    accepted
  have sourceAtRoute : hsame routeRead routeRead ∧ Cont C N routeRead :=
    ⟨hsame_refl routeRead, routeRoute⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row routeRead ∧ Cont C N routeRead)
          (fun row : BHist =>
            hsame row S ∨ hsame row L ∨ hsame row R ∨ hsame row D ∨ hsame row H ∨
              hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row routeRead)
          (fun row : BHist =>
            hsame row routeRead ∧ hsame H (append L R) ∧ Cont L R D ∧
              Cont D H C ∧ Cont C N routeRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro routeRead sourceAtRoute
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, transportSame, distinctionRoute, replayRoute, source.right⟩
  }
  exact ⟨cert, transportSame, distinctionRoute, replayRoute, routeRoute⟩

end BEDC.Derived.TraditionComparisonBoundaryUp
