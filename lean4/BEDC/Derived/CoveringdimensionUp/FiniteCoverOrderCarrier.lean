import BEDC.Derived.CoveringdimensionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionFiniteCoverOrderCarrier [AskSetup] [PackageSetup]
    (compactMetric epsilonNet metricRead regSeqRead realSeal nerve orderTable transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory metricRead ∧
    UnaryHistory regSeqRead ∧ UnaryHistory realSeal ∧ UnaryHistory nerve ∧
      UnaryHistory orderTable ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont compactMetric epsilonNet metricRead ∧ Cont metricRead regSeqRead realSeal ∧
            Cont epsilonNet nerve orderTable ∧ Cont transport replay provenance ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem CoveringDimensionFiniteCoverOrderRoot [AskSetup] [PackageSetup]
    {compactMetric epsilonNet metricRead regSeqRead realSeal nerve orderTable transport replay
      provenance localName rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionFiniteCoverOrderCarrier compactMetric epsilonNet metricRead regSeqRead
        realSeal nerve orderTable transport replay provenance localName bundle pkg ->
      Cont orderTable localName rootRead ->
        PkgSig bundle rootRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
                  hsame row regSeqRead ∨ hsame row realSeal ∨ hsame row nerve ∨
                    hsame row orderTable ∨ hsame row rootRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
                  Cont metricRead regSeqRead realSeal ∧ Cont epsilonNet nerve orderTable ∧
                    Cont orderTable localName rootRead ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle rootRead pkg)
              hsame ∧
            UnaryHistory rootRead := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg SemanticNameCert
  intro carrier orderLocalRoot rootPkg
  obtain ⟨compactUnary, epsilonUnary, metricUnary, regSeqUnary, realSealUnary, nerveUnary,
    orderUnary, _transportUnary, _replayUnary, _provenanceUnary, localNameUnary,
    compactEpsilonMetric, metricRegSeqReal, epsilonNerveOrder, _transportReplayProvenance,
    provenancePkg, _localNamePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed orderUnary localNameUnary orderLocalRoot
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row rootRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row compactMetric ∨ hsame row epsilonNet ∨ hsame row metricRead ∨
            hsame row regSeqRead ∨ hsame row realSeal ∨ hsame row nerve ∨
              hsame row orderTable ∨ hsame row rootRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont compactMetric epsilonNet metricRead ∧
            Cont metricRead regSeqRead realSeal ∧ Cont epsilonNet nerve orderTable ∧
              Cont orderTable localName rootRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle rootRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro rootRead ⟨hsame_refl rootRead, rootUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, compactEpsilonMetric, metricRegSeqReal, epsilonNerveOrder,
            orderLocalRoot, provenancePkg, rootPkg⟩
    }
  exact ⟨cert, rootUnary⟩

end BEDC.Derived.CoveringdimensionUp
