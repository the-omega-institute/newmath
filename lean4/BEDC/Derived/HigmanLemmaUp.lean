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

end BEDC.Derived.HigmanLemmaUp
