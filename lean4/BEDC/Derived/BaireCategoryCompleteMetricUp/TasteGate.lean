import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BaireCategoryCompleteMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BaireCategoryCompleteMetricCarrier [AskSetup] [PackageSetup]
    (B K M D S R Y E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory B ∧ UnaryHistory K ∧ UnaryHistory M ∧ UnaryHistory D ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory Y ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BaireCategoryCompleteMetricNameCert_obligations [AskSetup] [PackageSetup]
    {B K M D S R Y E H C P N denseRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BaireCategoryCompleteMetricCarrier B K M D S R Y E H C P N bundle pkg →
      Cont C N denseRead →
        PkgSig bundle denseRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row denseRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row B ∨ hsame row K ∨ hsame row M ∨ hsame row D ∨
                  hsame row S ∨ hsame row R ∨ hsame row Y ∨ hsame row E ∨
                    hsame row denseRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont C N denseRead ∧ PkgSig bundle denseRead pkg)
              hsame ∧
            UnaryHistory denseRead := by
  -- BEDC touchpoint anchor: BaireCategoryCompleteMetricCarrier BHist Cont PkgSig hsame SemanticNameCert
  intro carrier replayRoute densePkg
  obtain ⟨_bUnary, _kUnary, _mUnary, _dUnary, _sUnary, _rUnary, _yUnary, _eUnary,
    _hUnary, cUnary, _pUnary, nUnary, _provenancePkg, _namePkg⟩ := carrier
  have denseUnary : UnaryHistory denseRead :=
    unary_cont_closed cUnary nUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row denseRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row B ∨ hsame row K ∨ hsame row M ∨ hsame row D ∨
              hsame row S ∨ hsame row R ∨ hsame row Y ∨ hsame row E ∨
                hsame row denseRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C N denseRead ∧ PkgSig bundle denseRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro denseRead ⟨hsame_refl denseRead, denseUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayRoute, densePkg⟩
  }
  exact ⟨cert, denseUnary⟩

end BEDC.Derived.BaireCategoryCompleteMetricUp
