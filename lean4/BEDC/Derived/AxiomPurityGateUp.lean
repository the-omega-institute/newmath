import BEDC.Derived.AxiomPurityGateUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.AxiomPurityGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AxiomPurityGateNonescape [AskSetup] [PackageSetup]
    {T D F R L S H C P N reportRead refusalRead replacementRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont T D reportRead →
      Cont D F refusalRead →
        Cont R L replacementRead →
          Cont reportRead refusalRead auditRead →
            PkgSig bundle auditRead pkg →
              List.Mem (axiomPurityGateEncodeBHist T)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                List.Mem (axiomPurityGateEncodeBHist D)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                List.Mem (axiomPurityGateEncodeBHist F)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                List.Mem (axiomPurityGateEncodeBHist R)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                List.Mem (axiomPurityGateEncodeBHist L)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                List.Mem (axiomPurityGateEncodeBHist S)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                List.Mem (axiomPurityGateEncodeBHist H)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                List.Mem (axiomPurityGateEncodeBHist C)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                List.Mem (axiomPurityGateEncodeBHist P)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                List.Mem (axiomPurityGateEncodeBHist N)
                  (axiomPurityGateToEventFlow (AxiomPurityGateUp.mk T D F R L S H C P N)) ∧
                Cont T D reportRead ∧
                Cont D F refusalRead ∧
                Cont R L replacementRead ∧
                Cont reportRead refusalRead auditRead ∧
                PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist BMark Cont ProbeBundle Pkg PkgSig
  intro reportRoute refusalRoute replacementRoute auditRoute pkgRoute
  unfold axiomPurityGateToEventFlow
  exact
    ⟨List.Mem.tail _ (List.Mem.head _),
      List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))),
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))),
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))),
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))),
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))),
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))),
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _
                                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))))))))))),
      List.Mem.tail _
        (List.Mem.tail _
          (List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _
                            (List.Mem.tail _
                              (List.Mem.tail _
                                (List.Mem.tail _
                                  (List.Mem.tail _
                                    (List.Mem.tail _
                                      (List.Mem.tail _
                                        (List.Mem.tail _
                                          (List.Mem.tail _
                                            (List.Mem.head _))))))))))))))))))),
      reportRoute, refusalRoute, replacementRoute, auditRoute, pkgRoute⟩

theorem AxiomPurityGateBridgedHandoff [AskSetup] [PackageSetup]
    {T D F R L S H C P N reportRead refusalRead replacementRead auditRead
      bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory auditRead →
      UnaryHistory N →
        Cont T D reportRead →
          Cont D F refusalRead →
            Cont R L replacementRead →
              Cont reportRead refusalRead auditRead →
                Cont auditRead N bridgeRead →
                  PkgSig bundle bridgeRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row T ∨ hsame row D ∨ hsame row F ∨ hsame row R ∨
                            hsame row L ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                              hsame row P ∨ hsame row N ∨ hsame row bridgeRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont auditRead N bridgeRead ∧
                            PkgSig bundle bridgeRead pkg)
                        hsame ∧
                      UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro auditUnary nameUnary _reportRoute _refusalRoute _replacementRoute _auditRoute
    bridgeRoute bridgePkg
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed auditUnary nameUnary bridgeRoute
  have sourceAtBridge : hsame bridgeRead bridgeRead ∧ UnaryHistory bridgeRead :=
    ⟨hsame_refl bridgeRead, bridgeUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row T ∨ hsame row D ∨ hsame row F ∨ hsame row R ∨
              hsame row L ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont auditRead N bridgeRead ∧
              PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceAtBridge
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
                  (Or.inr
                    (Or.inr
                      (Or.inr (Or.inr (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bridgeRoute, bridgePkg⟩
  }
  exact ⟨cert, bridgeUnary⟩

end BEDC.Derived.AxiomPurityGateUp
