import BEDC.Derived.TheoryTransitionCertificateUp.TasteGate

namespace BEDC.Derived.TheoryTransitionCertificateUp

open BEDC.FKernel.Hist

theorem TheoryTransitionCertificate_conservative_preservation
    {T1 T2 S C D L F H R P N : BHist} :
    let packet := TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N
    theoryTransitionCertificateFields packet = [T1, T2, S, C, D, L, F, H, R, P, N] ∧
      List.Mem S (theoryTransitionCertificateFields packet) ∧
      List.Mem D (theoryTransitionCertificateFields packet) ∧
      List.Mem H (theoryTransitionCertificateFields packet) ∧
      List.Mem R (theoryTransitionCertificateFields packet) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · rfl
  · constructor
    · exact List.Mem.tail T1 (List.Mem.tail T2 (List.Mem.head [C, D, L, F, H, R, P, N]))
    · constructor
      · exact
          List.Mem.tail T1
            (List.Mem.tail T2
              (List.Mem.tail S
                (List.Mem.tail C (List.Mem.head [L, F, H, R, P, N]))))
      · constructor
        · exact
            List.Mem.tail T1
              (List.Mem.tail T2
                (List.Mem.tail S
                  (List.Mem.tail C
                    (List.Mem.tail D
                      (List.Mem.tail L
                        (List.Mem.tail F (List.Mem.head [R, P, N])))))))
        · exact
            List.Mem.tail T1
              (List.Mem.tail T2
                (List.Mem.tail S
                  (List.Mem.tail C
                    (List.Mem.tail D
                      (List.Mem.tail L
                        (List.Mem.tail F
                          (List.Mem.tail H (List.Mem.head [P, N]))))))))

end BEDC.Derived.TheoryTransitionCertificateUp
