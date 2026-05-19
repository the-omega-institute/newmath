import BEDC.Derived.TheoryTransitionCertificateUp.TasteGate
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TheoryTransitionCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TheoryTransitionCertificateNameCert_obligations
    {T1 T2 S C D L F H R P N : BHist} :
    SemanticNameCert
      (fun row : BHist =>
        hsame row N ∧
          ∃ packet : TheoryTransitionCertificateUp,
            packet = TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N ∧
              theoryTransitionCertificateFields packet = [T1, T2, S, C, D, L, F, H, R, P, N])
      (fun row : BHist =>
        hsame row N ∧
          ∃ packet : TheoryTransitionCertificateUp,
            packet = TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N ∧
              theoryTransitionCertificateToEventFlow packet =
                theoryTransitionCertificateToEventFlow
                  (TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N))
      (fun row : BHist =>
        hsame row N ∧
          List.Mem S (theoryTransitionCertificateFields
            (TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N)) ∧
          List.Mem D (theoryTransitionCertificateFields
            (TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N)) ∧
          List.Mem H (theoryTransitionCertificateFields
            (TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N)) ∧
          List.Mem R (theoryTransitionCertificateFields
            (TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N)))
      (fun row row' : BHist =>
        hsame row N ∧ hsame row' N ∧
          ∃ left right : TheoryTransitionCertificateUp,
            left = TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N ∧
              right = TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N ∧
                theoryTransitionCertificateToEventFlow left =
                  theoryTransitionCertificateToEventFlow right) := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨N, hsame_refl N,
            TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N, rfl, rfl⟩
      equiv_refl := by
        intro row source
        exact
          ⟨source.left, source.left,
            TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N,
            TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N, rfl, rfl, rfl⟩
      equiv_symm := by
        intro _row _row' same
        obtain ⟨rowName, rowName', left, right, leftEq, rightEq, eventEq⟩ := same
        exact ⟨rowName', rowName, right, left, rightEq, leftEq, eventEq.symm⟩
      equiv_trans := by
        intro _row _middle _row' leftSame rightSame
        obtain ⟨rowName, _middleName, _left, _middleLeft, _leftEq, _middleLeftEq,
          _leftEventEq⟩ := leftSame
        obtain ⟨_middleName', rowName', _middleRight, _right, _middleRightEq, rightEq,
          _rightEventEq⟩ := rightSame
        exact
          ⟨rowName, rowName',
            TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N,
            TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N, rfl, rfl, rfl⟩
      carrier_respects_equiv := by
        intro _row _row' same _source
        exact ⟨same.right.left, TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N, rfl, rfl⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨source.left,
          TheoryTransitionCertificateUp.mk T1 T2 S C D L F H R P N, rfl, rfl⟩
    ledger_sound := by
      intro row source
      exact
        ⟨source.left,
          List.Mem.tail T1 (List.Mem.tail T2 (List.Mem.head [C, D, L, F, H, R, P, N])),
          List.Mem.tail T1
            (List.Mem.tail T2
              (List.Mem.tail S
                (List.Mem.tail C (List.Mem.head [L, F, H, R, P, N])))),
          List.Mem.tail T1
            (List.Mem.tail T2
              (List.Mem.tail S
                (List.Mem.tail C
                  (List.Mem.tail D
                    (List.Mem.tail L
                      (List.Mem.tail F (List.Mem.head [R, P, N]))))))),
          List.Mem.tail T1
            (List.Mem.tail T2
              (List.Mem.tail S
                (List.Mem.tail C
                  (List.Mem.tail D
                    (List.Mem.tail L
                      (List.Mem.tail F
                        (List.Mem.tail H (List.Mem.head [P, N]))))))))⟩
  }

end BEDC.Derived.TheoryTransitionCertificateUp
