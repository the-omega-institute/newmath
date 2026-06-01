import BEDC.Derived.MetricCompletionMorphismUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionMorphismUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def MetricCompletionMorphismCarrier [AskSetup] [PackageSetup]
    (S T W R D M H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory S ∧ UnaryHistory T ∧ UnaryHistory W ∧ UnaryHistory R ∧
    UnaryHistory D ∧ UnaryHistory M ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ Cont S T W ∧ Cont W R D ∧
        Cont D M H ∧ Cont H C N ∧ PkgSig bundle P pkg

theorem MetricCompletionMorphismCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {S T W R D M H C P N cauchyRead mapRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionMorphismCarrier S T W R D M H C P N bundle pkg ->
      Cont S T cauchyRead ->
        Cont W R mapRead ->
          Cont mapRead M replayRead ->
            PkgSig bundle replayRead pkg ->
              SemanticNameCert
                    (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨
                        hsame row D ∨ hsame row M ∨ hsame row replayRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S T cauchyRead ∧ Cont W R mapRead ∧
                        Cont mapRead M replayRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle replayRead pkg)
                    hsame ∧
                  UnaryHistory cauchyRead ∧ UnaryHistory mapRead ∧
                    UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrier cauchyRoute mapRoute replayRoute replayPkg
  obtain ⟨SUnary, TUnary, WUnary, RUnary, _DUnary, MUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, _sourceTargetRoute, _windowReadbackRoute, _dyadicMapRoute,
    _transportReplayRoute, carrierPkg⟩ := carrier
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed SUnary TUnary cauchyRoute
  have mapUnary : UnaryHistory mapRead :=
    unary_cont_closed WUnary RUnary mapRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed mapUnary MUnary replayRoute
  have sourceReplay :
      (fun row : BHist => hsame row replayRead ∧ UnaryHistory row) replayRead := by
    exact ⟨hsame_refl replayRead, replayUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row T ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
              hsame row M ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S T cauchyRead ∧ Cont W R mapRead ∧
              Cont mapRead M replayRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead sourceReplay
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cauchyRoute, mapRoute, replayRoute, carrierPkg, replayPkg⟩
  }
  exact ⟨cert, cauchyUnary, mapUnary, replayUnary⟩

end BEDC.Derived.MetricCompletionMorphismUp
