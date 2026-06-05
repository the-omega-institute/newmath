import BEDC.Derived.AxiomPurityGateUp.TasteGate

namespace BEDC.Derived.AxiomPurityGateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package

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

end BEDC.Derived.AxiomPurityGateUp
