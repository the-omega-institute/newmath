import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.HigmanLemmaUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def HigmanLemmaCarrier [AskSetup] [PackageSetup]
    (S W E B D H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory E ∧ UnaryHistory B ∧
    UnaryHistory D ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem HigmanLemmaSubsequenceEmbeddingRoute [AskSetup] [PackageSetup]
    {S W E B D H C P N wordRead dependencyRead embeddingRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HigmanLemmaCarrier S W E B D H C P N bundle pkg ->
      Cont S W wordRead ->
        Cont wordRead D dependencyRead ->
          Cont dependencyRead E embeddingRead ->
            PkgSig bundle embeddingRead pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row embeddingRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row W ∨ hsame row E ∨ hsame row B ∨
                      hsame row D ∨ hsame row embeddingRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S W wordRead ∧
                      Cont wordRead D dependencyRead ∧
                        Cont dependencyRead E embeddingRead ∧
                          PkgSig bundle embeddingRead pkg)
                  hsame ∧
                UnaryHistory wordRead ∧ UnaryHistory dependencyRead ∧
                  UnaryHistory embeddingRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier wordRoute dependencyRoute embeddingRoute embeddingPkg
  obtain ⟨sUnary, wUnary, eUnary, _bUnary, dUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have wordUnary : UnaryHistory wordRead :=
    unary_cont_closed sUnary wUnary wordRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed wordUnary dUnary dependencyRoute
  have embeddingUnary : UnaryHistory embeddingRead :=
    unary_cont_closed dependencyUnary eUnary embeddingRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row embeddingRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row E ∨ hsame row B ∨ hsame row D ∨
              hsame row embeddingRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S W wordRead ∧ Cont wordRead D dependencyRead ∧
              Cont dependencyRead E embeddingRead ∧ PkgSig bundle embeddingRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro embeddingRead ⟨hsame_refl embeddingRead, embeddingUnary⟩
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
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, wordRoute, dependencyRoute, embeddingRoute, embeddingPkg⟩
  }
  exact ⟨cert, wordUnary, dependencyUnary, embeddingUnary⟩

theorem HigmanLemmaNameCertObligations [AskSetup] [PackageSetup]
    {S W E B D H C P N badRead replayRead nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HigmanLemmaCarrier S W E B D H C P N bundle pkg →
      Cont B D badRead →
        Cont badRead C replayRead →
          Cont replayRead N nameRead →
            PkgSig bundle nameRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    HigmanLemmaCarrier S W E B D H C P N bundle pkg ∧
                      hsame row nameRead)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row W ∨ hsame row E ∨ hsame row B ∨
                      hsame row D ∨ hsame row badRead ∨ hsame row replayRead ∨
                        hsame row nameRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont B D badRead ∧ Cont badRead C replayRead ∧
                      Cont replayRead N nameRead ∧ PkgSig bundle nameRead pkg)
                  hsame ∧
                UnaryHistory badRead ∧ UnaryHistory replayRead ∧ UnaryHistory nameRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier badRoute replayRoute nameRoute namePkg
  have carrierFull : HigmanLemmaCarrier S W E B D H C P N bundle pkg := carrier
  obtain ⟨_sUnary, _wUnary, _eUnary, bUnary, dUnary, _hUnary, cUnary, _pUnary,
    nUnary, _provenancePkg, _carrierNamePkg⟩ := carrier
  have badUnary : UnaryHistory badRead :=
    unary_cont_closed bUnary dUnary badRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed badUnary cUnary replayRoute
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed replayUnary nUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            HigmanLemmaCarrier S W E B D H C P N bundle pkg ∧ hsame row nameRead)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row E ∨ hsame row B ∨
              hsame row D ∨ hsame row badRead ∨ hsame row replayRead ∨
                hsame row nameRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont B D badRead ∧ Cont badRead C replayRead ∧
              Cont replayRead N nameRead ∧ PkgSig bundle nameRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro nameRead ⟨carrierFull, hsame_refl nameRead⟩
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
        exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.right))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨unary_transport_symm nameUnary source.right, badRoute, replayRoute, nameRoute,
          namePkg⟩
  }
  exact ⟨cert, badUnary, replayUnary, nameUnary⟩

theorem HigmanLemmaNormalizationFrontierHandoff [AskSetup] [PackageSetup]
    {S W E B D H C P N wordRead dependencyRead embeddingRead frontierRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HigmanLemmaCarrier S W E B D H C P N bundle pkg →
      Cont S W wordRead →
        Cont wordRead D dependencyRead →
          Cont dependencyRead E embeddingRead →
            Cont embeddingRead C frontierRead →
              PkgSig bundle frontierRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row W ∨ hsame row E ∨ hsame row D ∨
                        hsame row embeddingRead ∨ hsame row frontierRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S W wordRead ∧
                        Cont wordRead D dependencyRead ∧
                          Cont dependencyRead E embeddingRead ∧
                            Cont embeddingRead C frontierRead ∧
                              PkgSig bundle frontierRead pkg)
                    hsame ∧
                  UnaryHistory wordRead ∧ UnaryHistory dependencyRead ∧
                    UnaryHistory embeddingRead ∧ UnaryHistory frontierRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier wordRoute dependencyRoute embeddingRoute frontierRoute frontierPkg
  obtain ⟨sUnary, wUnary, eUnary, _bUnary, dUnary, _hUnary, cUnary, _pUnary,
    _nUnary, _provenancePkg, _namePkg⟩ := carrier
  have wordUnary : UnaryHistory wordRead :=
    unary_cont_closed sUnary wUnary wordRoute
  have dependencyUnary : UnaryHistory dependencyRead :=
    unary_cont_closed wordUnary dUnary dependencyRoute
  have embeddingUnary : UnaryHistory embeddingRead :=
    unary_cont_closed dependencyUnary eUnary embeddingRoute
  have frontierUnary : UnaryHistory frontierRead :=
    unary_cont_closed embeddingUnary cUnary frontierRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row frontierRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row E ∨ hsame row D ∨
              hsame row embeddingRead ∨ hsame row frontierRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S W wordRead ∧ Cont wordRead D dependencyRead ∧
              Cont dependencyRead E embeddingRead ∧ Cont embeddingRead C frontierRead ∧
                PkgSig bundle frontierRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro frontierRead ⟨hsame_refl frontierRead, frontierUnary⟩
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
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, wordRoute, dependencyRoute, embeddingRoute, frontierRoute,
          frontierPkg⟩
  }
  exact ⟨cert, wordUnary, dependencyUnary, embeddingUnary, frontierUnary⟩

end BEDC.Derived.HigmanLemmaUp
