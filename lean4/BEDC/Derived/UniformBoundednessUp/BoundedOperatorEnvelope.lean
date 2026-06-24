import BEDC.Derived.UniformBoundednessUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniformBoundednessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem UniformBoundednessBoundedOperatorEnvelope [AskSetup] [PackageSetup]
    {family pointwise baire norm regseq stream transport history replay provenance nameRow
      operatorRead boundRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniformBoundednessPacket family pointwise baire norm regseq stream transport history replay
        provenance nameRow bundle pkg →
      Cont family norm operatorRead →
        Cont operatorRead regseq boundRead →
          PkgSig bundle boundRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row boundRead ∧
                    UniformBoundednessPacket family pointwise baire norm regseq stream transport
                      history replay provenance nameRow bundle pkg)
                (fun row : BHist =>
                  hsame row family ∨ hsame row norm ∨ hsame row regseq ∨
                    hsame row operatorRead ∨ hsame row boundRead)
                (fun row : BHist =>
                  hsame row boundRead ∧ Cont family norm operatorRead ∧
                    Cont operatorRead regseq boundRead ∧ PkgSig bundle boundRead pkg)
                hsame ∧
              Cont family norm operatorRead ∧ Cont operatorRead regseq boundRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle boundRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet familyNormRoute operatorBoundRoute boundPkg
  rcases packet with
    ⟨sameNameHistory, familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
      transportHistoryReplay, replayProvenanceNameRow, provenancePkg, historyPkg⟩
  have packetAtBound :
      hsame boundRead boundRead ∧
        UniformBoundednessPacket family pointwise baire norm regseq stream transport history
          replay provenance nameRow bundle pkg := by
    exact
      ⟨hsame_refl boundRead, sameNameHistory, familyPointwiseBaire, baireNormRegseq,
        regseqStreamHistory, transportHistoryReplay, replayProvenanceNameRow, provenancePkg,
        historyPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row boundRead ∧
              UniformBoundednessPacket family pointwise baire norm regseq stream transport
                history replay provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row family ∨ hsame row norm ∨ hsame row regseq ∨
              hsame row operatorRead ∨ hsame row boundRead)
          (fun row : BHist =>
            hsame row boundRead ∧ Cont family norm operatorRead ∧
              Cont operatorRead regseq boundRead ∧ PkgSig bundle boundRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro boundRead packetAtBound
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
          ⟨hsame_trans (hsame_symm sameRows) source.left, sameNameHistory,
            familyPointwiseBaire, baireNormRegseq, regseqStreamHistory,
            transportHistoryReplay, replayProvenanceNameRow, provenancePkg, historyPkg⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, familyNormRoute, operatorBoundRoute, boundPkg⟩
  }
  exact ⟨cert, familyNormRoute, operatorBoundRoute, provenancePkg, boundPkg⟩

end BEDC.Derived.UniformBoundednessUp
