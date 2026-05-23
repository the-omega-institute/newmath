import BEDC.Derived.VerifiedOutputHarnessUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.VerifiedOutputHarnessUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem VerifiedOutputHarnessCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {I T M Q O C A R H K P N checked auditRead acceptedRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Q ->
      UnaryHistory O ->
        UnaryHistory C ->
          UnaryHistory A ->
            UnaryHistory R ->
              UnaryHistory K ->
                UnaryHistory N ->
                  Cont O C checked ->
                    Cont checked A auditRead ->
                      Cont auditRead R acceptedRead ->
                        Cont acceptedRead K namedRead ->
                          PkgSig bundle namedRead pkg ->
                            UnaryHistory checked ∧
                              UnaryHistory auditRead ∧
                                UnaryHistory acceptedRead ∧
                                  UnaryHistory namedRead ∧
                                    SemanticNameCert
                                      (fun row : BHist =>
                                        hsame row namedRead ∧ UnaryHistory row)
                                      (fun row : BHist =>
                                        hsame row checked ∨ hsame row auditRead ∨
                                          hsame row acceptedRead ∨ hsame row namedRead)
                                      (fun row : BHist =>
                                        PkgSig bundle namedRead pkg ∧
                                          hsame row namedRead)
                                      hsame ∧
                                      List.Mem (verifiedOutputHarnessEncodeBHist C)
                                        (verifiedOutputHarnessToEventFlow
                                          (VerifiedOutputHarnessUp.mk I T M Q O C A R H K P N)) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro _unaryQ unaryO unaryC unaryA unaryR unaryK _unaryN
  intro outputChecked checkedAudit auditAccepted acceptedNamed namedPkg
  have checkedUnary : UnaryHistory checked :=
    unary_cont_closed unaryO unaryC outputChecked
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed checkedUnary unaryA checkedAudit
  have acceptedUnary : UnaryHistory acceptedRead :=
    unary_cont_closed auditUnary unaryR auditAccepted
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed acceptedUnary unaryK acceptedNamed
  have sourceNamed :
      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row) namedRead := by
    exact ⟨hsame_refl namedRead, namedUnary⟩
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row checked ∨ hsame row auditRead ∨
            hsame row acceptedRead ∨ hsame row namedRead)
        (fun row : BHist => PkgSig bundle namedRead pkg ∧ hsame row namedRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro namedRead sourceNamed
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
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨namedPkg, source.left⟩
    }
  have checkerListed :
      List.Mem (verifiedOutputHarnessEncodeBHist C)
        (verifiedOutputHarnessToEventFlow
          (VerifiedOutputHarnessUp.mk I T M Q O C A R H K P N)) := by
    change
      List.Mem (verifiedOutputHarnessEncodeBHist C)
        [[BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist I,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist T,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist M,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist Q,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist O,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist C,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist A,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist R,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist H,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist K,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist P,
          [BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b1,
            BEDC.FKernel.Mark.BMark.b1, BEDC.FKernel.Mark.BMark.b0],
          verifiedOutputHarnessEncodeBHist N]
    exact
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _
          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))))))))
  exact ⟨checkedUnary, auditUnary, acceptedUnary, namedUnary, cert, checkerListed⟩

end BEDC.Derived.VerifiedOutputHarnessUp
