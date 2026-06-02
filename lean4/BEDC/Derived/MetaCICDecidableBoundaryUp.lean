import BEDC.Derived.MetaCICDecidableBoundaryUp.SiblingProvenance

namespace BEDC.Derived.MetaCICDecidableBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICDecidableBoundaryLedgerExactness [AskSetup] [PackageSetup]
    {T S B F R H C P N boundedRead ledgerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg →
      Cont B F boundedRead →
        Cont boundedRead R ledgerRead →
          PkgSig bundle ledgerRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row ledgerRead ∧
                    MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg)
                (fun row : BHist =>
                  hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨
                    hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row boundedRead ∨ hsame row ledgerRead)
                (fun row : BHist =>
                  hsame row ledgerRead ∧ Cont B F boundedRead ∧
                    Cont boundedRead R ledgerRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle ledgerRead pkg)
                hsame ∧
              UnaryHistory boundedRead ∧ UnaryHistory ledgerRead := by
  -- BEDC touchpoint anchor: MetaCICDecidableBoundaryCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier boundedFinishedRead readRefusalLedger ledgerPkg
  have carrierWhole := carrier
  obtain ⟨checkerUnary, structuralUnary, finishedUnary, refusalUnary, _transportUnary,
    _replayUnary, _provenanceUnary, _localNameUnary, checkerStructuralBounded,
    provenancePkg, _localNamePkg⟩ := carrier
  have boundedUnary : UnaryHistory B :=
    unary_cont_closed checkerUnary structuralUnary checkerStructuralBounded
  have boundedReadUnary : UnaryHistory boundedRead :=
    unary_cont_closed boundedUnary finishedUnary boundedFinishedRead
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed boundedReadUnary refusalUnary readRefusalLedger
  have sourceLedger :
      (fun row : BHist =>
        hsame row ledgerRead ∧
          MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg) ledgerRead := by
    exact ⟨hsame_refl ledgerRead, carrierWhole⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row ledgerRead ∧
              MetaCICDecidableBoundaryCarrier T S B F R H C P N bundle pkg)
          (fun row : BHist =>
            hsame row T ∨ hsame row S ∨ hsame row B ∨ hsame row F ∨ hsame row R ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row boundedRead ∨ hsame row ledgerRead)
          (fun row : BHist =>
            hsame row ledgerRead ∧ Cont B F boundedRead ∧
              Cont boundedRead R ledgerRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle ledgerRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead sourceLedger
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
        exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, boundedFinishedRead, readRefusalLedger, provenancePkg, ledgerPkg⟩
  }
  exact ⟨cert, boundedReadUnary, ledgerReadUnary⟩

end BEDC.Derived.MetaCICDecidableBoundaryUp
