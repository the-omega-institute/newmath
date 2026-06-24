import BEDC.Derived.UniformBoundednessUp

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem UniformBoundednessBaireHandoff [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row history ∧
              UniformBoundednessPacket family pointwise baire norm regseq stream transport
                history replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row baire ∨ hsame row norm ∨ hsame row regseq ∨ hsame row stream ∨
              hsame row history)
          (fun row : BHist =>
            hsame row history ∧ Cont family pointwise baire ∧ Cont baire norm regseq ∧
              Cont regseq stream history ∧ PkgSig bundle history pkg)
          hsame ∧
        Cont family pointwise baire ∧ Cont baire norm regseq ∧
          Cont regseq stream history ∧ PkgSig bundle history pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg SemanticNameCert hsame PkgSig
  intro packet
  rcases packet with
    ⟨sameNameHistory, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
      transportHistoryReplay, replayProvenanceNameRow, packageHistory⟩
  have packetAtHistory :
      hsame history history ∧
        UniformBoundednessPacket family pointwise baire norm regseq stream transport history
          replay provenance nameRow bundle pkg := by
    exact
      ⟨hsame_refl history, sameNameHistory, familyPointwiseBaire, baireNormRegseq,
        regseqStreamHistory, transportHistoryReplay, replayProvenanceNameRow,
        packageHistory⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row history ∧
              UniformBoundednessPacket family pointwise baire norm regseq stream transport
                history replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row baire ∨ hsame row norm ∨ hsame row regseq ∨ hsame row stream ∨
              hsame row history)
          (fun row : BHist =>
            hsame row history ∧ Cont family pointwise baire ∧ Cont baire norm regseq ∧
              Cont regseq stream history ∧ PkgSig bundle history pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro history packetAtHistory
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
            sameNameHistory, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
            transportHistoryReplay, replayProvenanceNameRow, packageHistory⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
          packageHistory⟩
  }
  exact ⟨cert, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory, packageHistory⟩

end BEDC.Derived.UniformBoundednessUp
