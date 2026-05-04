import BEDC.Derived.IntUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.IntUp

def IntHistoryCarrier (h : BEDC.FKernel.Hist.BHist) : Prop :=
  (Exists (fun m : BEDC.FKernel.Hist.BHist =>
    BEDC.FKernel.Unary.UnaryHistory m ∧
      BEDC.FKernel.Hist.hsame h (BEDC.FKernel.Hist.BHist.e0 m))) ∨
  (Exists (fun m : BEDC.FKernel.Hist.BHist =>
    BEDC.FKernel.Unary.UnaryHistory m ∧
      BEDC.FKernel.Hist.hsame h (BEDC.FKernel.Hist.BHist.e1 m)))

def IntHistoryClassifier
    (h k : BEDC.FKernel.Hist.BHist) : Prop :=
  (Exists (fun m : BEDC.FKernel.Hist.BHist =>
    Exists (fun n : BEDC.FKernel.Hist.BHist =>
      BEDC.FKernel.Unary.UnaryHistory m ∧ BEDC.FKernel.Unary.UnaryHistory n ∧
        BEDC.FKernel.Hist.hsame h (BEDC.FKernel.Hist.BHist.e0 m) ∧
          BEDC.FKernel.Hist.hsame k (BEDC.FKernel.Hist.BHist.e0 n) ∧
            BEDC.FKernel.Hist.hsame m n))) ∨
  (Exists (fun m : BEDC.FKernel.Hist.BHist =>
    Exists (fun n : BEDC.FKernel.Hist.BHist =>
      BEDC.FKernel.Unary.UnaryHistory m ∧ BEDC.FKernel.Unary.UnaryHistory n ∧
        BEDC.FKernel.Hist.hsame h (BEDC.FKernel.Hist.BHist.e1 m) ∧
          BEDC.FKernel.Hist.hsame k (BEDC.FKernel.Hist.BHist.e1 n) ∧
            BEDC.FKernel.Hist.hsame m n)))

theorem IntHistory_semanticNameCert :
    BEDC.FKernel.NameCert.SemanticNameCert IntHistoryCarrier IntHistoryCarrier
      IntHistoryCarrier IntHistoryClassifier ∧
      (forall m n : BEDC.FKernel.Hist.BHist,
        BEDC.FKernel.Unary.UnaryHistory m -> BEDC.FKernel.Unary.UnaryHistory n ->
          (IntHistoryClassifier (BEDC.FKernel.Hist.BHist.e0 m)
              (BEDC.FKernel.Hist.BHist.e1 n) -> False) ∧
          (IntHistoryClassifier (BEDC.FKernel.Hist.BHist.e1 m)
              (BEDC.FKernel.Hist.BHist.e0 n) -> False)) := by
  have zeroEmptyCarrier : IntHistoryCarrier
      (BEDC.FKernel.Hist.BHist.e0 BEDC.FKernel.Hist.BHist.Empty) := by
    exact Or.inl
      (Exists.intro BEDC.FKernel.Hist.BHist.Empty
        (And.intro BEDC.FKernel.Unary.unary_empty
          (BEDC.FKernel.Hist.hsame_refl
            (BEDC.FKernel.Hist.BHist.e0 BEDC.FKernel.Hist.BHist.Empty))))
  have cert :
      BEDC.FKernel.NameCert.SemanticNameCert IntHistoryCarrier IntHistoryCarrier
        IntHistoryCarrier IntHistoryClassifier := by
    constructor
    · constructor
      · exact Exists.intro
          (BEDC.FKernel.Hist.BHist.e0 BEDC.FKernel.Hist.BHist.Empty) zeroEmptyCarrier
      · intro h carrier
        cases carrier with
        | inl zero =>
            cases zero with
            | intro m data =>
                exact Or.inl
                  (Exists.intro m
                    (Exists.intro m
                      (And.intro data.left
                        (And.intro data.left
                          (And.intro data.right
                            (And.intro data.right
                              (BEDC.FKernel.Hist.hsame_refl m)))))))
        | inr one =>
            cases one with
            | intro m data =>
                exact Or.inr
                  (Exists.intro m
                    (Exists.intro m
                      (And.intro data.left
                        (And.intro data.left
                          (And.intro data.right
                            (And.intro data.right
                              (BEDC.FKernel.Hist.hsame_refl m)))))))
      · intro h k classified
        cases classified with
        | inl zero =>
            cases zero with
            | intro m rest =>
                cases rest with
                | intro n data =>
                    exact Or.inl
                      (Exists.intro n
                        (Exists.intro m
                          (And.intro data.right.left
                            (And.intro data.left
                              (And.intro data.right.right.right.left
                                (And.intro data.right.right.left
                                  (BEDC.FKernel.Hist.hsame_symm
                                    data.right.right.right.right)))))))
        | inr one =>
            cases one with
            | intro m rest =>
                cases rest with
                | intro n data =>
                    exact Or.inr
                      (Exists.intro n
                        (Exists.intro m
                          (And.intro data.right.left
                            (And.intro data.left
                              (And.intro data.right.right.right.left
                                (And.intro data.right.right.left
                                  (BEDC.FKernel.Hist.hsame_symm
                                    data.right.right.right.right)))))))
      · intro h k r classifiedHK classifiedKR
        cases classifiedHK with
        | inl zeroHK =>
            cases zeroHK with
            | intro m restHK =>
                cases restHK with
                | intro n dataHK =>
                    cases classifiedKR with
                    | inl zeroKR =>
                        cases zeroKR with
                        | intro p restKR =>
                            cases restKR with
                            | intro q dataKR =>
                                have sameMiddleTags :
                                    BEDC.FKernel.Hist.hsame
                                      (BEDC.FKernel.Hist.BHist.e0 n)
                                      (BEDC.FKernel.Hist.BHist.e0 p) :=
                                  BEDC.FKernel.Hist.hsame_trans
                                    (BEDC.FKernel.Hist.hsame_symm
                                      dataHK.right.right.right.left)
                                    dataKR.right.right.left
                                have sameNP : BEDC.FKernel.Hist.hsame n p :=
                                  Iff.mp BEDC.FKernel.Hist.hsame_e0_iff sameMiddleTags
                                have sameMQ : BEDC.FKernel.Hist.hsame m q :=
                                  BEDC.FKernel.Hist.hsame_trans dataHK.right.right.right.right
                                    (BEDC.FKernel.Hist.hsame_trans sameNP
                                      dataKR.right.right.right.right)
                                exact Or.inl
                                  (Exists.intro m
                                    (Exists.intro q
                                      (And.intro dataHK.left
                                        (And.intro dataKR.right.left
                                          (And.intro dataHK.right.right.left
                                            (And.intro dataKR.right.right.right.left
                                              sameMQ))))))
                    | inr oneKR =>
                        cases oneKR with
                        | intro p restKR =>
                            cases restKR with
                            | intro q dataKR =>
                                have mixed :
                                    BEDC.FKernel.Hist.hsame
                                      (BEDC.FKernel.Hist.BHist.e0 n)
                                      (BEDC.FKernel.Hist.BHist.e1 p) :=
                                  BEDC.FKernel.Hist.hsame_trans
                                    (BEDC.FKernel.Hist.hsame_symm
                                      dataHK.right.right.right.left)
                                    dataKR.right.right.left
                                exact False.elim (BEDC.FKernel.Hist.not_hsame_e0_e1 mixed)
        | inr oneHK =>
            cases oneHK with
            | intro m restHK =>
                cases restHK with
                | intro n dataHK =>
                    cases classifiedKR with
                    | inl zeroKR =>
                        cases zeroKR with
                        | intro p restKR =>
                            cases restKR with
                            | intro q dataKR =>
                                have mixed :
                                    BEDC.FKernel.Hist.hsame
                                      (BEDC.FKernel.Hist.BHist.e1 n)
                                      (BEDC.FKernel.Hist.BHist.e0 p) :=
                                  BEDC.FKernel.Hist.hsame_trans
                                    (BEDC.FKernel.Hist.hsame_symm
                                      dataHK.right.right.right.left)
                                    dataKR.right.right.left
                                exact False.elim (BEDC.FKernel.Hist.not_hsame_e1_e0 mixed)
                    | inr oneKR =>
                        cases oneKR with
                        | intro p restKR =>
                            cases restKR with
                            | intro q dataKR =>
                                have sameMiddleTags :
                                    BEDC.FKernel.Hist.hsame
                                      (BEDC.FKernel.Hist.BHist.e1 n)
                                      (BEDC.FKernel.Hist.BHist.e1 p) :=
                                  BEDC.FKernel.Hist.hsame_trans
                                    (BEDC.FKernel.Hist.hsame_symm
                                      dataHK.right.right.right.left)
                                    dataKR.right.right.left
                                have sameNP : BEDC.FKernel.Hist.hsame n p :=
                                  Iff.mp BEDC.FKernel.Hist.hsame_e1_iff sameMiddleTags
                                have sameMQ : BEDC.FKernel.Hist.hsame m q :=
                                  BEDC.FKernel.Hist.hsame_trans dataHK.right.right.right.right
                                    (BEDC.FKernel.Hist.hsame_trans sameNP
                                      dataKR.right.right.right.right)
                                exact Or.inr
                                  (Exists.intro m
                                    (Exists.intro q
                                      (And.intro dataHK.left
                                        (And.intro dataKR.right.left
                                          (And.intro dataHK.right.right.left
                                            (And.intro dataKR.right.right.right.left
                                              sameMQ))))))
      · intro h k classified _carrierH
        cases classified with
        | inl zero =>
            cases zero with
            | intro _m rest =>
                cases rest with
                | intro n data =>
                    exact Or.inl (Exists.intro n
                      (And.intro data.right.left data.right.right.right.left))
        | inr one =>
            cases one with
            | intro _m rest =>
                cases rest with
                | intro n data =>
                    exact Or.inr (Exists.intro n
                      (And.intro data.right.left data.right.right.right.left))
    · intro h carrier
      exact carrier
    · intro h carrier
      exact carrier
  constructor
  · exact cert
  · intro m n _unaryM _unaryN
    constructor
    · intro classified
      cases classified with
      | inl zero =>
          cases zero with
          | intro _p rest =>
              cases rest with
              | intro q data =>
                  exact BEDC.FKernel.Hist.not_hsame_e1_e0 data.right.right.right.left
      | inr one =>
          cases one with
          | intro p rest =>
              cases rest with
              | intro _q data =>
                  exact BEDC.FKernel.Hist.not_hsame_e0_e1 data.right.right.left
    · intro classified
      cases classified with
      | inl zero =>
          cases zero with
          | intro p rest =>
              cases rest with
              | intro _q data =>
                  exact BEDC.FKernel.Hist.not_hsame_e1_e0 data.right.right.left
      | inr one =>
          cases one with
          | intro _p rest =>
              cases rest with
              | intro q data =>
                  exact BEDC.FKernel.Hist.not_hsame_e0_e1 data.right.right.right.left

end BEDC.Derived.IntUp
