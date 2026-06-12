import BEDC.Derived.RealNameClassifierUp

namespace BEDC.Derived.RealNameClassifierUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealNameClassifierLedgerExhaustion [AskSetup] [PackageSetup]
    {source stream rat dyadic tolerance refinement sealRow transport replay provenance
      localName ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealNameClassifierUp source stream rat dyadic tolerance refinement sealRow transport replay
        provenance localName bundle pkg →
      Cont tolerance sealRow ledgerRead →
        PkgSig bundle ledgerRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row source ∨ hsame row stream ∨ hsame row rat ∨ hsame row dyadic ∨
                  hsame row tolerance ∨ hsame row refinement ∨ hsame row sealRow ∨
                    hsame row ledgerRead ∨ hsame row localName)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont tolerance sealRow ledgerRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                    PkgSig bundle ledgerRead pkg)
              hsame ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier ledgerRoute ledgerPkg
  obtain ⟨_sourceUnary, _streamUnary, _ratUnary, _dyadicUnary, toleranceUnary,
    _refinementUnary, sealUnary, _transportUnary, _replayUnary, _provenanceUnary,
    _localNameUnary, _sourceStreamReplay, _ratDyadicTolerance, _toleranceRefinementSeal,
    _transportReplay, provenancePkg, localNamePkg⟩ := carrier
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed toleranceUnary sealUnary ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row source ∨ hsame row stream ∨ hsame row rat ∨ hsame row dyadic ∨
              hsame row tolerance ∨ hsame row refinement ∨ hsame row sealRow ∨
                hsame row ledgerRead ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont tolerance sealRow ledgerRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg ∧
                PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
                  (Or.inr
                    (Or.inr
                      (Or.inl sourceData.left)))))))
    ledger_sound := by
      intro _row sourceData
      exact ⟨sourceData.right, ledgerRoute, provenancePkg, localNamePkg, ledgerPkg⟩
  }
  exact ⟨cert, ledgerUnary⟩

end BEDC.Derived.RealNameClassifierUp
