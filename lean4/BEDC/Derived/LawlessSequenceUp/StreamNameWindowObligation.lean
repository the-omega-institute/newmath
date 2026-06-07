import BEDC.Derived.LawlessSequenceUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequenceStreamNameWindowObligation [AskSetup] [PackageSetup]
    {W B I H C P N windowRead digitRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawless_sequence_stream_name_handoff_carrier W B I H C P N bundle pkg →
      Cont I W windowRead →
        Cont windowRead B digitRead →
          Cont digitRead C replayRead →
            PkgSig bundle replayRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row I ∨ hsame row W ∨ hsame row B ∨ hsame row H ∨
                      hsame row C ∨ hsame row replayRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont I W windowRead ∧
                      Cont windowRead B digitRead ∧ Cont digitRead C replayRead ∧
                        PkgSig bundle replayRead pkg)
                  hsame ∧ UnaryHistory windowRead ∧ UnaryHistory digitRead ∧
                UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrierRows indexWindow windowDigit digitReplay replayPkg
  obtain ⟨WUnary, BUnary, IUnary, _HUnary, CUnary, _PUnary, _NUnary, _provenancePkg,
    _localNamePkg⟩ := carrierRows
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed IUnary WUnary indexWindow
  have digitUnary : UnaryHistory digitRead :=
    unary_cont_closed windowUnary BUnary windowDigit
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed digitUnary CUnary digitReplay
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row W ∨ hsame row B ∨ hsame row H ∨ hsame row C ∨
              hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I W windowRead ∧ Cont windowRead B digitRead ∧
              Cont digitRead C replayRead ∧ PkgSig bundle replayRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, indexWindow, windowDigit, digitReplay, replayPkg⟩
  }
  exact ⟨cert, windowUnary, digitUnary, replayUnary⟩

end BEDC.Derived.LawlessSequenceUp
