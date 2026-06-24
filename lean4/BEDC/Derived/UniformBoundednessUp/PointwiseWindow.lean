import BEDC.Derived.UniformBoundednessUp

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem UniformBoundednessPointwiseWindow [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow
      scheduledRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg →
      Cont pointwise stream scheduledRead →
        PkgSig bundle scheduledRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row scheduledRead ∧
                  UniformBoundednessPacket family pointwise baire norm regseq stream transport
                    history replay provenance nameRow bundle pkg)
              (fun row : BHist =>
                hsame row pointwise ∨ hsame row stream ∨ hsame row scheduledRead ∨
                  hsame row history)
              (fun row : BHist =>
                hsame row scheduledRead ∧ Cont pointwise stream scheduledRead ∧
                  PkgSig bundle scheduledRead pkg)
              hsame ∧ Cont family pointwise baire ∧ Cont pointwise stream scheduledRead ∧
            PkgSig bundle scheduledRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet pointwiseStreamScheduled scheduledPkg
  rcases packet with
    ⟨sameNameHistory, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
      transportHistoryReplay, replayProvenanceNameRow, packageProvenance, packageHistory⟩
  have packetAtScheduled :
      hsame scheduledRead scheduledRead ∧
        UniformBoundednessPacket family pointwise baire norm regseq stream transport history
          replay provenance nameRow bundle pkg := by
    exact
      ⟨hsame_refl scheduledRead, sameNameHistory, familyPointwiseBaire, baireNormRegseq,
        regseqStreamHistory, transportHistoryReplay, replayProvenanceNameRow,
        packageProvenance, packageHistory⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row scheduledRead ∧
              UniformBoundednessPacket family pointwise baire norm regseq stream transport
                history replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row pointwise ∨ hsame row stream ∨ hsame row scheduledRead ∨
              hsame row history)
          (fun row : BHist =>
            hsame row scheduledRead ∧ Cont pointwise stream scheduledRead ∧
              PkgSig bundle scheduledRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scheduledRead packetAtScheduled
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            sameNameHistory, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
            transportHistoryReplay, replayProvenanceNameRow, packageProvenance,
            packageHistory⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inl sourceRow.left))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, pointwiseStreamScheduled, scheduledPkg⟩
  }
  exact ⟨cert, familyPointwiseBaire, pointwiseStreamScheduled, scheduledPkg⟩

end BEDC.Derived.UniformBoundednessUp
