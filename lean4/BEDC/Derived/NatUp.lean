import BEDC.FKernel.Cont.Cancellation
import BEDC.FKernel.ExternalBinary
import BEDC.FKernel.Unary

namespace BEDC.Derived.NatUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

def NatUnaryStrictPrefix (h k : BHist) : Prop :=
  ∃ tail : BHist, UnaryHistory tail ∧ (tail = BHist.Empty → False) ∧ Cont h tail k

theorem NatUnaryStrictPrefix_one_step {h : BHist} :
    UnaryHistory h -> NatUnaryStrictPrefix h (BHist.e1 h) := by
  intro _uh
  exact ⟨BHist.e1 BHist.Empty, unary_e1_closed unary_empty,
    (fun empty => by cases empty), cont_intro rfl⟩

theorem NatUnaryStrictPrefix_asymm {h k : BHist} :
    NatUnaryStrictPrefix h k -> NatUnaryStrictPrefix k h -> False := by
  intro forward backward
  cases forward with
  | intro forwardTail forwardData =>
      cases forwardData with
      | intro _forwardUnary forwardStrictData =>
          cases forwardStrictData with
          | intro forwardNonempty forwardCont =>
              cases backward with
              | intro backwardTail backwardData =>
                  cases backwardData with
                  | intro _backwardUnary backwardStrictData =>
                      cases backwardStrictData with
                      | intro _backwardNonempty backwardCont =>
                          have same : hsame h k :=
                            cont_mutual_extension_hsame forwardCont backwardCont
                          have unitAtTarget : Cont h BHist.Empty k :=
                            cont_result_hsame_transport (cont_right_unit h) same
                          have forwardEmpty : forwardTail = BHist.Empty :=
                            cont_left_cancel forwardCont unitAtTarget
                          exact forwardNonempty forwardEmpty

theorem NatUnaryStrictPrefix_empty_right_absurd {h : BHist} :
    NatUnaryStrictPrefix h BHist.Empty -> False := by
  intro strict
  cases strict with
  | intro tail data =>
      have parts := cont_empty_result_inversion data.right.right
      exact data.right.left parts.right

theorem NatUnaryStrictPrefix_tail_endpoint_hsame_absurd {h k tail : BHist} :
    UnaryHistory tail -> (tail = BHist.Empty -> False) -> Cont h tail k ->
      hsame h k -> False := by
  intro _tailUnary tailNonempty tailCont sameEndpoint
  have unitAtEndpoint : Cont h BHist.Empty k :=
    cont_result_hsame_transport (cont_right_unit h) sameEndpoint
  have tailEmpty : hsame tail BHist.Empty := cont_left_cancel tailCont unitAtEndpoint
  exact tailNonempty tailEmpty

theorem NatUnaryStrictPrefix_e1_inversion {h k : BHist} :
    NatUnaryStrictPrefix (BHist.e1 h) (BHist.e1 k) -> NatUnaryStrictPrefix h k := by
  intro strict
  cases strict with
  | intro tail data =>
      cases data with
      | intro tailUnary strictData =>
          cases strictData with
          | intro tailNonempty tailCont =>
              cases tail with
              | Empty =>
                  exact False.elim (tailNonempty rfl)
              | e0 tail =>
                  exact False.elim (unary_no_zero_extension tailUnary)
              | e1 tail =>
                  have tailInnerUnary : UnaryHistory tail := unary_e1_inversion tailUnary
                  have tailStep :
                      append (BHist.e1 h) tail = BHist.e1 (append h tail) :=
                    unary_append_e1_left (h := tail) (k := h) tailInnerUnary
                  have loweredCont : Cont h (BHist.e1 tail) k := by
                    exact cont_intro ((BHist.e1.inj tailCont).trans tailStep)
                  exact ⟨BHist.e1 tail, tailUnary, (fun empty => by cases empty), loweredCont⟩

theorem NatUnaryStrictPrefix_e1_endpoint_hsame_absurd {h k : BHist} :
    NatUnaryStrictPrefix (BHist.e1 h) (BHist.e1 k) -> hsame h k -> False := by
  intro strict sameTail
  have lowered : NatUnaryStrictPrefix h k := NatUnaryStrictPrefix_e1_inversion strict
  cases lowered with
  | intro tail data =>
      exact NatUnaryStrictPrefix_tail_endpoint_hsame_absurd
        data.left data.right.left data.right.right sameTail

theorem NatUnaryStrictPrefix_e1_congr {h k : BHist} :
    NatUnaryStrictPrefix h k -> NatUnaryStrictPrefix (BHist.e1 h) (BHist.e1 k) := by
  intro strict
  cases strict with
  | intro tail data =>
      cases data with
      | intro tailUnary strictData =>
          cases strictData with
          | intro tailNonempty tailCont =>
              exact
                ⟨tail, tailUnary, tailNonempty,
                  cont_intro
                    ((congrArg BHist.e1 tailCont).trans
                      (unary_append_e1_left (h := tail) (k := h) tailUnary).symm)⟩

theorem NatUnaryStrictPrefix_e0_inversion {h k : BHist} :
    NatUnaryStrictPrefix (BHist.e0 h) (BHist.e0 k) -> NatUnaryStrictPrefix h k := by
  intro strict
  cases strict with
  | intro tail data =>
      cases data with
      | intro tailUnary strictData =>
          cases strictData with
          | intro tailNonempty tailCont =>
              cases tail with
              | Empty =>
                  exact False.elim (tailNonempty rfl)
              | e0 tail =>
                  exact False.elim (unary_no_zero_extension tailUnary)
              | e1 tail =>
                  cases tailCont

theorem NatUnaryStrictPrefix_append_tail_trans {h k l leftTail rightTail : BHist} :
    UnaryHistory leftTail -> (leftTail = BHist.Empty -> False) -> Cont h leftTail k ->
      UnaryHistory rightTail -> (rightTail = BHist.Empty -> False) -> Cont k rightTail l ->
        NatUnaryStrictPrefix h l ∧ Cont h (append leftTail rightTail) l := by
  intro leftUnary leftNonempty leftCont rightUnary _rightNonempty rightCont
  have joinedCont : Cont h (append leftTail rightTail) l := by
    cases leftCont
    cases rightCont
    exact cont_intro (append_assoc h leftTail rightTail)
  have joinedStrict : NatUnaryStrictPrefix h l := by
    exact ⟨append leftTail rightTail, unary_append_closed leftUnary rightUnary,
      (fun appendedEmpty => leftNonempty (append_eq_empty_iff.mp appendedEmpty).left), joinedCont⟩
  exact And.intro joinedStrict joinedCont

theorem NatUnaryStrictPrefix_target_unary {h k : BHist} :
    UnaryHistory h -> NatUnaryStrictPrefix h k -> UnaryHistory k := by
  intro hUnary strict
  cases strict with
  | intro tail data =>
      exact unary_cont_closed hUnary data.left data.right.right

theorem NatUnaryStrictPrefix_trans_composite_tail {h k l : BHist} :
    NatUnaryStrictPrefix h k -> NatUnaryStrictPrefix k l ->
      exists tail : BHist,
        UnaryHistory tail ∧ (tail = BHist.Empty -> False) ∧ Cont h tail l ∧
          NatUnaryStrictPrefix h l := by
  intro leftStrict rightStrict
  cases leftStrict with
  | intro leftTail leftData =>
      cases leftData with
      | intro leftUnary leftRest =>
          cases leftRest with
          | intro leftNonempty leftCont =>
              cases rightStrict with
              | intro rightTail rightData =>
                  cases rightData with
                  | intro rightUnary rightRest =>
                      cases rightRest with
                      | intro rightNonempty rightCont =>
                          have joined :=
                            NatUnaryStrictPrefix_append_tail_trans leftUnary leftNonempty
                              leftCont rightUnary rightNonempty rightCont
                          exact Exists.intro (append leftTail rightTail)
                            (And.intro (unary_append_closed leftUnary rightUnary)
                              (And.intro
                                (fun appendedEmpty =>
                                  leftNonempty (append_eq_empty_iff.mp appendedEmpty).left)
                                (And.intro joined.right joined.left)))

theorem NatUnaryStrictPrefix_cont_hsame_transport {h h' k k' tail : BHist} :
    UnaryHistory tail -> (tail = BHist.Empty -> False) -> Cont h tail k ->
      hsame h h' -> hsame k k' -> NatUnaryStrictPrefix h' k' := by
  intro tailUnary tailNonempty tailCont sameH sameK
  exact Exists.intro tail
    (And.intro tailUnary
      (And.intro tailNonempty
        (cont_hsame_transport sameH (hsame_refl tail) sameK tailCont)))

theorem NatUnaryPrefix_total {h k : BHist} :
    UnaryHistory h -> UnaryHistory k ->
      (exists tail : BHist, UnaryHistory tail /\ Cont h tail k) \/
        (exists tail : BHist, UnaryHistory tail /\ Cont k tail h) := by
  intro uh uk
  induction h generalizing k with
  | Empty =>
      exact Or.inl ⟨k, uk, cont_left_unit k⟩
  | e0 h ih =>
      cases uh
  | e1 h ih =>
      cases k with
      | Empty =>
          exact Or.inr ⟨BHist.e1 h, uh, cont_left_unit (BHist.e1 h)⟩
      | e0 k =>
          cases uk
      | e1 k =>
          have recResult := ih (k := k) uh uk
          cases recResult with
          | inl left =>
              cases left with
              | intro tail data =>
                  cases data with
                  | intro tailUnary tailCont =>
                      have base : Cont (BHist.e1 h) tail (BHist.e1 (append h tail)) := by
                        exact cont_intro
                          (unary_append_e1_left (h := tail) (k := h) tailUnary).symm
                      have same : hsame (BHist.e1 (append h tail)) (BHist.e1 k) := by
                        exact hsame_e1_congr tailCont.symm
                      exact Or.inl
                        ⟨tail, tailUnary, cont_result_hsame_transport base same⟩
          | inr right =>
              cases right with
              | intro tail data =>
                  cases data with
                  | intro tailUnary tailCont =>
                      have base : Cont (BHist.e1 k) tail (BHist.e1 (append k tail)) := by
                        exact cont_intro
                          (unary_append_e1_left (h := tail) (k := k) tailUnary).symm
                      have same : hsame (BHist.e1 (append k tail)) (BHist.e1 h) := by
                        exact hsame_e1_congr tailCont.symm
                      exact Or.inr
                        ⟨tail, tailUnary, cont_result_hsame_transport base same⟩

theorem NatUnaryPrefix_trichotomy_hsame_strict {h k : BHist} :
    UnaryHistory h -> UnaryHistory k ->
      hsame h k ∨ NatUnaryStrictPrefix h k ∨ NatUnaryStrictPrefix k h := by
  intro uh uk
  have total := NatUnaryPrefix_total uh uk
  cases total with
  | inl left =>
      cases left with
      | intro tail data =>
          cases data with
          | intro tailUnary tailCont =>
              cases tail with
              | Empty =>
                  have same : hsame k h := cont_deterministic tailCont (cont_right_unit h)
                  exact Or.inl (hsame_symm same)
              | e0 tail =>
                  exact False.elim (unary_no_zero_extension tailUnary)
              | e1 tail =>
                  exact Or.inr
                    (Or.inl
                      ⟨BHist.e1 tail, tailUnary, (fun empty => by cases empty), tailCont⟩)
  | inr right =>
      cases right with
      | intro tail data =>
          cases data with
          | intro tailUnary tailCont =>
              cases tail with
              | Empty =>
                  have same : hsame h k := cont_deterministic tailCont (cont_right_unit k)
                  exact Or.inl same
              | e0 tail =>
                  exact False.elim (unary_no_zero_extension tailUnary)
              | e1 tail =>
                  exact Or.inr
                    (Or.inr
                      ⟨BHist.e1 tail, tailUnary, (fun empty => by cases empty), tailCont⟩)

theorem NatUnaryPrefix_directed_common_upper {h k : BHist} :
    UnaryHistory h -> UnaryHistory k ->
      exists upper : BHist, And (UnaryHistory upper)
        (And (exists tail : BHist, And (UnaryHistory tail) (Cont h tail upper))
          (exists tail : BHist, And (UnaryHistory tail) (Cont k tail upper))) := by
  intro uh uk
  have total := NatUnaryPrefix_total uh uk
  cases total with
  | inl left =>
      cases left with
      | intro tail data =>
          cases data with
          | intro tailUnary tailCont =>
              exact Exists.intro k
                (And.intro uk
                  (And.intro
                    (Exists.intro tail (And.intro tailUnary tailCont))
                    (Exists.intro BHist.Empty
                      (And.intro unary_empty (cont_right_unit k)))))
  | inr right =>
      cases right with
      | intro tail data =>
          cases data with
          | intro tailUnary tailCont =>
              exact Exists.intro h
                (And.intro uh
                  (And.intro
                    (Exists.intro BHist.Empty
                      (And.intro unary_empty (cont_right_unit h)))
                    (Exists.intro tail (And.intro tailUnary tailCont))))

theorem NatUnaryPrefix_cont_tail_cases {h k tail : BHist} :
    UnaryHistory tail -> Cont h tail k -> hsame h k ∨ NatUnaryStrictPrefix h k := by
  intro tailUnary tailCont
  cases tail with
  | Empty =>
      exact Or.inl tailCont.symm
  | e0 tail =>
      cases tailUnary
  | e1 tail =>
      exact Or.inr
        ⟨BHist.e1 tail, tailUnary, (fun empty => by cases empty), tailCont⟩

theorem NatUp_unary_standard_bridge :
    (BEDC.FKernel.ExternalBinary.bwordLength BHist.Empty = 0) ∧
      (forall h : BHist, UnaryHistory h ->
        BEDC.FKernel.ExternalBinary.bwordLength (BHist.e1 h) =
          Nat.succ (BEDC.FKernel.ExternalBinary.bwordLength h)) ∧
      (forall h : BHist, UnaryHistory (BHist.e0 h) -> False) ∧
      (forall {h k : BHist}, UnaryHistory h -> UnaryHistory k ->
        (hsame h k <->
          BEDC.FKernel.ExternalBinary.bwordLength h =
            BEDC.FKernel.ExternalBinary.bwordLength k)) ∧
      (forall {h t k : BHist}, UnaryHistory h -> UnaryHistory t -> Cont h t k ->
        BEDC.FKernel.ExternalBinary.bwordLength k =
          BEDC.FKernel.ExternalBinary.bwordLength h +
            BEDC.FKernel.ExternalBinary.bwordLength t) := by
  have lengthEq_hsame :
      forall {h k : BHist}, UnaryHistory h -> UnaryHistory k ->
        BEDC.FKernel.ExternalBinary.bwordLength h =
          BEDC.FKernel.ExternalBinary.bwordLength k -> hsame h k := by
    intro h k unaryH unaryK lengthEq
    induction h generalizing k with
    | Empty =>
        cases k with
        | Empty =>
            rfl
        | e0 k =>
            cases unaryK
        | e1 k =>
            cases lengthEq
    | e0 h =>
        cases unaryH
    | e1 h ih =>
        cases k with
        | Empty =>
            cases lengthEq
        | e0 k =>
            cases unaryK
        | e1 k =>
            exact hsame_e1_congr (ih unaryH unaryK (Nat.succ.inj lengthEq))
  constructor
  · rfl
  · constructor
    · intro h _unaryH
      rfl
    · constructor
      · intro h unaryZero
        exact unary_no_zero_extension unaryZero
      · constructor
        · intro h k unaryH unaryK
          constructor
          · intro same
            cases same
            rfl
          · intro lengthEq
            exact lengthEq_hsame unaryH unaryK lengthEq
        · intro h t k _unaryH _unaryT contHTK
          exact (congrArg BEDC.FKernel.ExternalBinary.bwordLength contHTK).trans
            (BEDC.FKernel.ExternalBinary.bwordLength_append h t)

theorem NatUp_StdBridge {h k tail : BHist} :
    UnaryHistory h -> UnaryHistory k -> UnaryHistory tail -> Cont h tail k ->
      (UnaryClassifierSpec h k ∨ NatUnaryStrictPrefix h k) ∧
        (BEDC.FKernel.ExternalBinary.bwordLength k =
          BEDC.FKernel.ExternalBinary.bwordLength h +
            BEDC.FKernel.ExternalBinary.bwordLength tail) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryClassifierSpec NatUnaryStrictPrefix
  intro unaryH unaryK unaryTail continuation
  constructor
  · cases NatUnaryPrefix_cont_tail_cases unaryTail continuation with
    | inl same =>
        exact Or.inl ⟨unaryH, unaryK, same⟩
    | inr strict =>
        exact Or.inr strict
  · exact NatUp_unary_standard_bridge.right.right.right.right unaryH unaryTail continuation

theorem NatUp_mature_unary_recursion_package {h : BHist} :
    UnaryHistory h ->
      (hsame h BHist.Empty ∨ ∃ pred : BHist, UnaryHistory pred ∧ hsame h (BHist.e1 pred)) ∧
        (UnaryHistory (BHist.e0 h) -> False) ∧
          (forall {tail result : BHist}, UnaryHistory tail -> Cont h tail result ->
            UnaryHistory result ∧
              BEDC.FKernel.ExternalBinary.bwordLength result =
                BEDC.FKernel.ExternalBinary.bwordLength h +
                  BEDC.FKernel.ExternalBinary.bwordLength tail) := by
  intro unaryH
  constructor
  · cases h with
    | Empty =>
        exact Or.inl rfl
    | e0 h =>
        exact False.elim (unary_no_zero_extension unaryH)
    | e1 pred =>
        exact Or.inr (Exists.intro pred (And.intro (unary_e1_inversion unaryH) rfl))
  · constructor
    · intro zeroUnary
      exact unary_no_zero_extension zeroUnary
    · intro tail result unaryTail continuation
      exact And.intro (unary_cont_closed unaryH unaryTail continuation)
        (NatUp_unary_standard_bridge.right.right.right.right unaryH unaryTail continuation)

end BEDC.Derived.NatUp
