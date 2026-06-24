import BEDC.Derived.UniformBoundednessUp

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem UniformBoundednessPublicBoundary [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg →
      Cont stream history publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                hsame row publicRead ∧
                  UniformBoundednessPacket family pointwise baire norm regseq stream transport
                    history replay provenance nameRow bundle pkg)
              (fun row : BHist =>
                hsame row family ∨ hsame row pointwise ∨ hsame row baire ∨
                  hsame row norm ∨ hsame row regseq ∨ hsame row stream ∨
                    hsame row publicRead)
              (fun row : BHist =>
                hsame row publicRead ∧ Cont family pointwise baire ∧
                  Cont baire norm regseq ∧ Cont regseq stream history ∧
                    Cont stream history publicRead ∧ PkgSig bundle publicRead pkg)
              hsame ∧ Cont family pointwise baire ∧ Cont baire norm regseq ∧
            Cont regseq stream history ∧ Cont stream history publicRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet streamHistoryPublic publicPkg
  rcases packet with
    ⟨sameNameHistory, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
      transportHistoryReplay, replayProvenanceNameRow, packageProvenance, packageHistory⟩
  have packetAtPublic :
      hsame publicRead publicRead ∧
        UniformBoundednessPacket family pointwise baire norm regseq stream transport history
          replay provenance nameRow bundle pkg := by
    exact
      ⟨hsame_refl publicRead, sameNameHistory, familyPointwiseBaire, baireNormRegseq,
        regseqStreamHistory, transportHistoryReplay, replayProvenanceNameRow,
        packageProvenance, packageHistory⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row publicRead ∧
              UniformBoundednessPacket family pointwise baire norm regseq stream transport
                history replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row family ∨ hsame row pointwise ∨ hsame row baire ∨
              hsame row norm ∨ hsame row regseq ∨ hsame row stream ∨
                hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont family pointwise baire ∧
              Cont baire norm regseq ∧ Cont regseq stream history ∧
                Cont stream history publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead packetAtPublic
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.left, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
          streamHistoryPublic, publicPkg⟩
  }
  exact
    ⟨cert, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory, streamHistoryPublic⟩

end BEDC.Derived.UniformBoundednessUp
