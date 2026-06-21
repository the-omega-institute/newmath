import BEDC.Derived.MetaCICCriticalPathUp.Core

namespace BEDC.Derived.MetaCICCriticalPathUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MetaCICCriticalPathLocalDiamondDischargeCover [AskSetup] [PackageSetup]
    {socket candidateResidual sourceOrder downstreamBoundary coverRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory socket ->
      UnaryHistory candidateResidual ->
        UnaryHistory sourceOrder ->
          UnaryHistory downstreamBoundary ->
            Cont socket candidateResidual sourceOrder ->
              Cont sourceOrder downstreamBoundary coverRead ->
                PkgSig bundle coverRead pkg ->
                  SemanticNameCert
                      (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row socket ∨ hsame row candidateResidual ∨
                          hsame row sourceOrder ∨ hsame row downstreamBoundary ∨
                            hsame row coverRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont socket candidateResidual sourceOrder ∧
                          Cont sourceOrder downstreamBoundary coverRead ∧
                            PkgSig bundle coverRead pkg)
                      hsame ∧
                    UnaryHistory sourceOrder ∧ UnaryHistory coverRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro socketUnary candidateUnary sourceUnary downstreamUnary socketCandidateSource
    sourceDownstreamCover coverPackage
  have coverUnary : UnaryHistory coverRead :=
    unary_cont_closed sourceUnary downstreamUnary sourceDownstreamCover
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row coverRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row socket ∨ hsame row candidateResidual ∨ hsame row sourceOrder ∨
              hsame row downstreamBoundary ∨ hsame row coverRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont socket candidateResidual sourceOrder ∧
              Cont sourceOrder downstreamBoundary coverRead ∧ PkgSig bundle coverRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro coverRead ⟨hsame_refl coverRead, coverUnary⟩
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
      exact ⟨source.right, socketCandidateSource, sourceDownstreamCover, coverPackage⟩
  }
  exact ⟨cert, sourceUnary, coverUnary⟩

end BEDC.Derived.MetaCICCriticalPathUp
