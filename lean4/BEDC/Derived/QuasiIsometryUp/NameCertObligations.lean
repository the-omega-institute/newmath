import BEDC.Derived.QuasiIsometryUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.QuasiIsometryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem QuasiIsometryNamecertObligations [AskSetup] [PackageSetup]
    {sourceMetric targetMetric coarseGraph distortion coarseSurjectivity distanceReadback
      completionFacing transport replay provenance name : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory sourceMetric →
      UnaryHistory targetMetric →
        UnaryHistory coarseGraph →
          Cont coarseGraph distortion coarseSurjectivity →
            PkgSig bundle provenance pkg →
              SemanticNameCert
                (fun row : BHist => hsame row coarseGraph ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row sourceMetric ∨ hsame row targetMetric ∨ hsame row coarseGraph ∨
                    hsame row coarseSurjectivity)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
                hsame := by
  -- BEDC touchpoint anchor: QuasiIsometryUp BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro _sourceUnary _targetUnary coarseUnary _coarseRoute provenancePkg
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro coarseGraph ⟨hsame_refl coarseGraph, coarseUnary⟩
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
      right
      right
      left
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg⟩
  }

end BEDC.Derived.QuasiIsometryUp
