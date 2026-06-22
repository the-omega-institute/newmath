import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierScopedKernelRoute [AskSetup] [PackageSetup]
    {source stream rat dyadic tolerance refinement sealRow transport replay provenance localName
      scopedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg →
      Cont localName provenance scopedRead →
        PkgSig bundle scopedRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row stream ∨ hsame row rat ∨ hsame row dyadic ∨
                  hsame row tolerance ∨ hsame row refinement ∨ hsame row sealRow ∨
                    hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                      hsame row localName ∨ hsame row scopedRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont localName provenance scopedRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle scopedRead pkg)
              hsame ∧ UnaryHistory scopedRead := by
  -- BEDC touchpoint anchor: RealNameClassifierUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier scopedRoute scopedPkg
  obtain ⟨_sourceUnary, _streamUnary, _ratUnary, _dyadicUnary, _toleranceUnary,
    _refinementUnary, _sealUnary, _transportUnary, _replayUnary, provenanceUnary,
    localNameUnary, _sourceStreamReplay, _ratDyadicTolerance, _toleranceRefinementSeal,
    _transportReplay, provenancePkg, localNamePkg⟩ := carrier
  have scopedUnary : UnaryHistory scopedRead :=
    unary_cont_closed localNameUnary provenanceUnary scopedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row stream ∨ hsame row rat ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row refinement ∨ hsame row sealRow ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName ∨ hsame row scopedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont localName provenance scopedRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                PkgSig bundle scopedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopedRead ⟨hsame_refl scopedRead, scopedUnary⟩
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
        intro _row _other sameRows sourceData
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceData.left,
            unary_transport sourceData.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceData
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact sourceData.left
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, scopedRoute, provenancePkg, localNamePkg, scopedPkg⟩
  }
  exact ⟨cert, scopedUnary⟩

end BEDC.Derived.RealNameClassifierUp
