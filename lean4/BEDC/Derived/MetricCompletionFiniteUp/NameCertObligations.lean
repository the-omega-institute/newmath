import BEDC.Derived.MetricCompletionFiniteUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.MetricCompletionFiniteUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetricCompletionFiniteCarrier_obligation_boundary [AskSetup] [PackageSetup]
    (F : MetricCompletionFiniteUp) {M B W E R S H C P N sourceRead readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    metricCompletionFiniteFields F = [M, B, W, E, R, S, H, C, P, N] →
      UnaryHistory M →
        UnaryHistory B →
          UnaryHistory W →
            UnaryHistory E →
              UnaryHistory S →
                Cont M B sourceRead →
                  Cont W E readback →
                    PkgSig bundle P pkg →
                      UnaryHistory sourceRead ∧ UnaryHistory readback ∧
                        Cont M B sourceRead ∧ Cont W E readback ∧
                          PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig UnaryHistory ProbeBundle
  intro fieldRows metricUnary basisUnary windowUnary embeddingUnary _selectorUnary
    sourceRoute readbackRoute provenancePkg
  cases F with
  | mk _metric _basis _window _embedding _readback _selector _transport _replay
      _provenance _localName =>
      change
        [_metric, _basis, _window, _embedding, _readback, _selector, _transport,
          _replay, _provenance, _localName] =
          [M, B, W, E, R, S, H, C, P, N] at fieldRows
      have sourceUnary : UnaryHistory sourceRead :=
        unary_cont_closed metricUnary basisUnary sourceRoute
      have readbackUnary : UnaryHistory readback :=
        unary_cont_closed windowUnary embeddingUnary readbackRoute
      exact
        ⟨sourceUnary, readbackUnary, sourceRoute, readbackRoute, provenancePkg⟩

def MetricCompletionFiniteCarrier [AskSetup] [PackageSetup]
    (metric cauchyBasis window embedding readback selector transport replay provenance localName :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory metric ∧ UnaryHistory cauchyBasis ∧ UnaryHistory window ∧
    UnaryHistory embedding ∧ UnaryHistory readback ∧ UnaryHistory selector ∧
      UnaryHistory transport ∧ UnaryHistory replay ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem MetricCompletionFiniteCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {metric cauchyBasis window embedding readback selector transport replay provenance localName :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetricCompletionFiniteCarrier metric cauchyBasis window embedding readback selector transport
        replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row cauchyBasis ∨ hsame row window ∨
              hsame row embedding ∨ hsame row readback ∨ hsame row selector ∨
                hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame ∧
        PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier
  obtain ⟨_metricUnary, _basisUnary, _windowUnary, _embeddingUnary, _readbackUnary,
    _selectorUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    provenancePkg, localNamePkg⟩ := carrier
  have localSource :
      (fun row : BHist => hsame row localName ∧ UnaryHistory row) localName := by
    exact ⟨hsame_refl localName, localNameUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row cauchyBasis ∨ hsame row window ∨
              hsame row embedding ∨ hsame row readback ∨ hsame row selector ∨
                hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localName localSource
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, provenancePkg, localNamePkg⟩

end BEDC.Derived.MetricCompletionFiniteUp
