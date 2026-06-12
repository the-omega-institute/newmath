import BEDC.Derived.LawlessSequenceUp.ChoiceFreeCarrierObligation
import BEDC.FKernel.NameCert

namespace BEDC.Derived.LawlessSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem LawlessSequenceRealNonescape [AskSetup] [PackageSetup]
    {W B I H C P N windowRead digitRead replayRead choiceRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    lawless_sequence_stream_name_handoff_carrier W B I H C P N bundle pkg →
      Cont I W windowRead →
        Cont windowRead B digitRead →
          Cont digitRead C replayRead →
            Cont replayRead N choiceRead →
              Cont choiceRead P realRead →
                PkgSig bundle realRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row I ∨ hsame row W ∨ hsame row B ∨ hsame row C ∨
                          hsame row N ∨ hsame row choiceRead ∨ hsame row realRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont I W windowRead ∧
                          Cont windowRead B digitRead ∧ Cont digitRead C replayRead ∧
                            Cont replayRead N choiceRead ∧ Cont choiceRead P realRead ∧
                              PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg)
                      hsame ∧
                    UnaryHistory windowRead ∧ UnaryHistory digitRead ∧
                      UnaryHistory replayRead ∧ UnaryHistory choiceRead ∧
                        UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrierRows indexWindow windowDigit digitReplay replayChoice choiceReal realPkg
  obtain ⟨windowUnary, boolUnary, indexUnary, _transportUnary, replayUnary,
    provenanceUnary, localNameUnary, provenancePkg, _localNamePkg⟩ := carrierRows
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed indexUnary windowUnary indexWindow
  have digitReadUnary : UnaryHistory digitRead :=
    unary_cont_closed windowReadUnary boolUnary windowDigit
  have replayReadUnary : UnaryHistory replayRead :=
    unary_cont_closed digitReadUnary replayUnary digitReplay
  have choiceReadUnary : UnaryHistory choiceRead :=
    unary_cont_closed replayReadUnary localNameUnary replayChoice
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed choiceReadUnary provenanceUnary choiceReal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row I ∨ hsame row W ∨ hsame row B ∨ hsame row C ∨
              hsame row N ∨ hsame row choiceRead ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont I W windowRead ∧
              Cont windowRead B digitRead ∧ Cont digitRead C replayRead ∧
                Cont replayRead N choiceRead ∧ Cont choiceRead P realRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle realRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro row source
      exact
        ⟨source.right, indexWindow, windowDigit, digitReplay, replayChoice, choiceReal,
          provenancePkg, realPkg⟩
  }
  exact
    ⟨cert, windowReadUnary, digitReadUnary, replayReadUnary, choiceReadUnary,
      realReadUnary⟩

end BEDC.Derived.LawlessSequenceUp
