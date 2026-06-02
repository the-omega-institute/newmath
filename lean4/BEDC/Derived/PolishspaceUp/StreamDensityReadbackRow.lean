import BEDC.Derived.PolishspaceUp.RootUnblockSurface
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PolishspaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PolishSpaceStreamDensityReadbackRow [AskSetup] [PackageSetup]
    {metric complete separable stream readback ledger transport replay provenance localName
      denseRead streamDensityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PolishSpaceRootUnblockSurface metric complete separable stream readback ledger transport
        replay provenance localName bundle pkg →
      Cont separable stream denseRead →
        Cont denseRead readback streamDensityRead →
          SemanticNameCert
              (fun row : BHist => hsame row streamDensityRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row separable ∨ hsame row stream ∨ hsame row readback ∨
                  hsame row ledger ∨ hsame row streamDensityRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle localName pkg)
              hsame ∧
            UnaryHistory denseRead ∧ UnaryHistory streamDensityRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro surface separableStreamDense denseReadbackStreamDensity
  obtain ⟨_metricUnary, _completeUnary, separableUnary, streamUnary, readbackUnary,
    _ledgerUnary, _transportUnary, _metricComplete, _metricSeparable,
    _ledgerTransportReplay, provenancePkg, localNamePkg⟩ := surface
  have denseReadUnary : UnaryHistory denseRead :=
    unary_cont_closed separableUnary streamUnary separableStreamDense
  have streamDensityReadUnary : UnaryHistory streamDensityRead :=
    unary_cont_closed denseReadUnary readbackUnary denseReadbackStreamDensity
  have sourceStreamDensityRead :
      (fun row : BHist => hsame row streamDensityRead ∧ UnaryHistory row)
          streamDensityRead := by
    exact ⟨hsame_refl streamDensityRead, streamDensityReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row streamDensityRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row separable ∨ hsame row stream ∨ hsame row readback ∨
              hsame row ledger ∨ hsame row streamDensityRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro streamDensityRead sourceStreamDensityRead
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, denseReadUnary, streamDensityReadUnary⟩

end BEDC.Derived.PolishspaceUp
