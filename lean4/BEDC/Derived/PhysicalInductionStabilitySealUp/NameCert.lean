import BEDC.Derived.PhysicalInductionStabilitySealUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.PhysicalInductionStabilitySealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem PhysicalInductionStabilitySealNameCert_obligations
    {H F C S L R T P N : BHist} :
    SemanticNameCert
      (fun row : BHist =>
        hsame row N ∧
          ∃ packet : PhysicalInductionStabilitySealUp,
            packet = PhysicalInductionStabilitySealUp.mk H F C S L R T P N ∧
              physicalInductionStabilitySealFields packet = [H, F, C, S, L, R, T, P, N])
      (fun row : BHist =>
        hsame row N ∧
          ∃ packet : PhysicalInductionStabilitySealUp,
            packet = PhysicalInductionStabilitySealUp.mk H F C S L R T P N ∧
              physicalInductionStabilitySealToEventFlow packet =
                physicalInductionStabilitySealToEventFlow
                  (PhysicalInductionStabilitySealUp.mk H F C S L R T P N))
      (fun row : BHist =>
        hsame row N ∧
          List.Mem L (physicalInductionStabilitySealFields
            (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) ∧
          List.Mem R (physicalInductionStabilitySealFields
            (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) ∧
          List.Mem T (physicalInductionStabilitySealFields
            (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) ∧
          List.Mem P (physicalInductionStabilitySealFields
            (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)))
      (fun row row' : BHist =>
        hsame row N ∧ hsame row' N ∧
          ∃ left right : PhysicalInductionStabilitySealUp,
            left = PhysicalInductionStabilitySealUp.mk H F C S L R T P N ∧
              right = PhysicalInductionStabilitySealUp.mk H F C S L R T P N ∧
                physicalInductionStabilitySealToEventFlow left =
                  physicalInductionStabilitySealToEventFlow right) := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited := by
        exact
          ⟨N, hsame_refl N,
            PhysicalInductionStabilitySealUp.mk H F C S L R T P N, rfl, rfl⟩
      equiv_refl := by
        intro row source
        exact
          ⟨source.left, source.left,
            PhysicalInductionStabilitySealUp.mk H F C S L R T P N,
            PhysicalInductionStabilitySealUp.mk H F C S L R T P N, rfl, rfl, rfl⟩
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
            PhysicalInductionStabilitySealUp.mk H F C S L R T P N,
            PhysicalInductionStabilitySealUp.mk H F C S L R T P N, rfl, rfl, rfl⟩
      carrier_respects_equiv := by
        intro _row _row' same _source
        exact
          ⟨same.right.left,
            PhysicalInductionStabilitySealUp.mk H F C S L R T P N, rfl, rfl⟩
    }
    pattern_sound := by
      intro row source
      exact
        ⟨source.left,
          PhysicalInductionStabilitySealUp.mk H F C S L R T P N, rfl, rfl⟩
    ledger_sound := by
      intro row source
      exact
        ⟨source.left,
          List.Mem.tail H
            (List.Mem.tail F
              (List.Mem.tail C
                (List.Mem.tail S (List.Mem.head [R, T, P, N])))),
          List.Mem.tail H
            (List.Mem.tail F
              (List.Mem.tail C
                (List.Mem.tail S
                  (List.Mem.tail L (List.Mem.head [T, P, N]))))),
          List.Mem.tail H
            (List.Mem.tail F
              (List.Mem.tail C
                (List.Mem.tail S
                  (List.Mem.tail L
                    (List.Mem.tail R (List.Mem.head [P, N])))))),
          List.Mem.tail H
            (List.Mem.tail F
              (List.Mem.tail C
                (List.Mem.tail S
                  (List.Mem.tail L
                    (List.Mem.tail R
                      (List.Mem.tail T (List.Mem.head [N])))))))⟩
  }

theorem PhysicalInductionStabilitySealScopedRoute
    {H F C S L R T P N scopedRead : BHist} :
    Cont R N scopedRead →
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              ∃ packet : PhysicalInductionStabilitySealUp,
                packet = PhysicalInductionStabilitySealUp.mk H F C S L R T P N ∧
                  physicalInductionStabilitySealFields packet =
                    [H, F, C, S, L, R, T, P, N])
          (fun row : BHist =>
            hsame row N ∧
              List.Mem C
                (physicalInductionStabilitySealFields
                  (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) ∧
                List.Mem T
                  (physicalInductionStabilitySealFields
                    (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)))
          (fun row : BHist =>
            hsame row N ∧ Cont R N scopedRead ∧
              List.Mem P
                (physicalInductionStabilitySealFields
                  (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)))
          hsame ∧
        List.Mem H
          (physicalInductionStabilitySealFields
            (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) ∧
          List.Mem F
            (physicalInductionStabilitySealFields
              (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) ∧
            List.Mem C
              (physicalInductionStabilitySealFields
                (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) ∧
              Cont R N scopedRead := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  intro scopedRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨N, hsame_refl N,
              PhysicalInductionStabilitySealUp.mk H F C S L R T P N, rfl, rfl⟩
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
              PhysicalInductionStabilitySealUp.mk H F C S L R T P N, rfl, rfl⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left,
            List.Mem.tail H (List.Mem.tail F (List.Mem.head [S, L, R, T, P, N])),
            List.Mem.tail H
              (List.Mem.tail F
                (List.Mem.tail C
                  (List.Mem.tail S
                    (List.Mem.tail L
                      (List.Mem.tail R (List.Mem.head [P, N]))))))⟩
      ledger_sound := by
        intro _row source
        exact
          ⟨source.left, scopedRoute,
            List.Mem.tail H
              (List.Mem.tail F
                (List.Mem.tail C
                  (List.Mem.tail S
                    (List.Mem.tail L
                      (List.Mem.tail R
                        (List.Mem.tail T (List.Mem.head [N])))))))⟩
    }
  · exact
      ⟨List.Mem.head [F, C, S, L, R, T, P, N],
        List.Mem.tail H (List.Mem.head [C, S, L, R, T, P, N]),
        List.Mem.tail H (List.Mem.tail F (List.Mem.head [S, L, R, T, P, N])),
        scopedRoute⟩

theorem PhysicalInductionStabilitySealPublicExport
    {H F C S L R T P N publicRead : BHist} :
    Cont R P publicRead →
      SemanticNameCert
          (fun row : BHist =>
            hsame row publicRead ∧
              ∃ packet : PhysicalInductionStabilitySealUp,
                packet = PhysicalInductionStabilitySealUp.mk H F C S L R T P N ∧
                  List.Mem R (physicalInductionStabilitySealFields packet))
          (fun row : BHist =>
            hsame row H ∨ hsame row F ∨ hsame row C ∨ hsame row S ∨
              hsame row L ∨ hsame row R ∨ hsame row T ∨ hsame row P ∨
                hsame row N ∨ hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont R P publicRead ∧
              List.Mem N
                (physicalInductionStabilitySealFields
                  (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)))
          hsame ∧
        List.Mem R
          (physicalInductionStabilitySealFields
            (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) ∧
          List.Mem P
            (physicalInductionStabilitySealFields
              (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) ∧
            List.Mem N
              (physicalInductionStabilitySealFields
                (PhysicalInductionStabilitySealUp.mk H F C S L R T P N)) := by
  -- BEDC touchpoint anchor: BHist hsame Cont SemanticNameCert
  intro publicRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact
            ⟨publicRead, hsame_refl publicRead,
              PhysicalInductionStabilitySealUp.mk H F C S L R T P N, rfl,
              List.Mem.tail H
                (List.Mem.tail F
                  (List.Mem.tail C
                    (List.Mem.tail S
                      (List.Mem.tail L (List.Mem.head [T, P, N])))))⟩
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
          obtain ⟨packet, packetEq, rMember⟩ := source.right
          exact
            ⟨hsame_trans (hsame_symm sameRows) source.left,
              packet, packetEq, rMember⟩
      }
      pattern_sound := by
        intro _row source
        right
        right
        right
        right
        right
        right
        right
        right
        right
        exact source.left
      ledger_sound := by
        intro _row source
        exact
          ⟨source.left, publicRoute,
            List.Mem.tail H
              (List.Mem.tail F
                (List.Mem.tail C
                  (List.Mem.tail S
                    (List.Mem.tail L
                      (List.Mem.tail R
                        (List.Mem.tail T
                          (List.Mem.tail P (List.Mem.head []))))))))⟩
    }
  · exact
      ⟨List.Mem.tail H
          (List.Mem.tail F
            (List.Mem.tail C
              (List.Mem.tail S (List.Mem.tail L (List.Mem.head [T, P, N]))))),
        List.Mem.tail H
          (List.Mem.tail F
            (List.Mem.tail C
              (List.Mem.tail S
                (List.Mem.tail L
                  (List.Mem.tail R (List.Mem.tail T (List.Mem.head [N]))))))),
        List.Mem.tail H
          (List.Mem.tail F
            (List.Mem.tail C
              (List.Mem.tail S
                (List.Mem.tail L
                  (List.Mem.tail R
                    (List.Mem.tail T (List.Mem.tail P (List.Mem.head []))))))))⟩

end BEDC.Derived.PhysicalInductionStabilitySealUp
