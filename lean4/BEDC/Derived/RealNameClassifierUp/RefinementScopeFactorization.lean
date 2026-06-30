import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierRefinementScopeFactorization [AskSetup] [PackageSetup]
    {source stream rat dyadic tolerance refinement sealRow transport replay provenance
      localName scopeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg →
      Cont tolerance refinement sealRow →
        Cont sealRow provenance scopeRead →
          PkgSig bundle scopeRead pkg →
            SemanticNameCert
              (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row stream ∨ hsame row dyadic ∨
                  hsame row tolerance ∨ hsame row refinement ∨ hsame row sealRow ∨
                    hsame row scopeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont tolerance refinement sealRow ∧
                  Cont sealRow provenance scopeRead ∧ PkgSig bundle scopeRead pkg)
              hsame ∧ UnaryHistory scopeRead := by
  -- BEDC touchpoint anchor: RealNameClassifierUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier toleranceSealRoute scopeRoute scopedPkg
  obtain ⟨_sourceUnary, _streamUnary, _ratUnary, _dyadicUnary, _toleranceUnary,
    _refinementUnary, sealUnary, _transportUnary, _replayUnary, provenanceUnary,
    _localNameUnary, _sourceStreamReplay, _ratDyadicTolerance, _carrierToleranceSeal,
    _transportReplay, _provenancePkg, _localNamePkg⟩ := carrier
  have scopedUnary : UnaryHistory scopeRead :=
    unary_cont_closed sealUnary provenanceUnary scopeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scopeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row stream ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row refinement ∨ hsame row sealRow ∨
                hsame row scopeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tolerance refinement sealRow ∧
              Cont sealRow provenance scopeRead ∧ PkgSig bundle scopeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scopeRead ⟨hsame_refl scopeRead, scopedUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceData.left)))))
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, toleranceSealRoute, scopeRoute, scopedPkg⟩
  }
  exact ⟨cert, scopedUnary⟩

end BEDC.Derived.RealNameClassifierUp
