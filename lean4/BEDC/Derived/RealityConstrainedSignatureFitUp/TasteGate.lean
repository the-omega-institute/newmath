import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealityConstrainedSignatureFitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealityConstrainedSignatureFitUp : Type where
  | mk : (S A M G P C H Q N : BHist) → RealityConstrainedSignatureFitUp
  deriving DecidableEq

def realityConstrainedSignatureFitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realityConstrainedSignatureFitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realityConstrainedSignatureFitEncodeBHist h

def realityConstrainedSignatureFitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realityConstrainedSignatureFitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realityConstrainedSignatureFitDecodeBHist tail)

private theorem realityConstrainedSignatureFitDecode_encode_bhist :
    ∀ h : BHist,
      realityConstrainedSignatureFitDecodeBHist
        (realityConstrainedSignatureFitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem realityConstrainedSignatureFit_mk_congr
    {S S' A A' M M' G G' P P' C C' H H' Q Q' N N' : BHist}
    (hS : S' = S) (hA : A' = A) (hM : M' = M) (hG : G' = G) (hP : P' = P)
    (hC : C' = C) (hH : H' = H) (hQ : Q' = Q) (hN : N' = N) :
    RealityConstrainedSignatureFitUp.mk S' A' M' G' P' C' H' Q' N' =
      RealityConstrainedSignatureFitUp.mk S A M G P C H Q N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hS
  cases hA
  cases hM
  cases hG
  cases hP
  cases hC
  cases hH
  cases hQ
  cases hN
  rfl

def realityConstrainedSignatureFitFields :
    RealityConstrainedSignatureFitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RealityConstrainedSignatureFitUp.mk S A M G P C H Q N => [S, A, M, G, P, C, H, Q, N]

def realityConstrainedSignatureFitToEventFlow :
    RealityConstrainedSignatureFitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (realityConstrainedSignatureFitFields x).map realityConstrainedSignatureFitEncodeBHist

def realityConstrainedSignatureFitFromEventFlow :
    EventFlow → Option RealityConstrainedSignatureFitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _S :: [] => none
  | _S :: _A :: [] => none
  | _S :: _A :: _M :: [] => none
  | _S :: _A :: _M :: _G :: [] => none
  | _S :: _A :: _M :: _G :: _P :: [] => none
  | _S :: _A :: _M :: _G :: _P :: _C :: [] => none
  | _S :: _A :: _M :: _G :: _P :: _C :: _H :: [] => none
  | _S :: _A :: _M :: _G :: _P :: _C :: _H :: _Q :: [] => none
  | S :: A :: M :: G :: P :: C :: H :: Q :: N :: [] =>
      some
        (RealityConstrainedSignatureFitUp.mk
          (realityConstrainedSignatureFitDecodeBHist S)
          (realityConstrainedSignatureFitDecodeBHist A)
          (realityConstrainedSignatureFitDecodeBHist M)
          (realityConstrainedSignatureFitDecodeBHist G)
          (realityConstrainedSignatureFitDecodeBHist P)
          (realityConstrainedSignatureFitDecodeBHist C)
          (realityConstrainedSignatureFitDecodeBHist H)
          (realityConstrainedSignatureFitDecodeBHist Q)
          (realityConstrainedSignatureFitDecodeBHist N))
  | _S :: _A :: _M :: _G :: _P :: _C :: _H :: _Q :: _N :: _extra :: _rest => none

private theorem realityConstrainedSignatureFit_round_trip :
    ∀ x : RealityConstrainedSignatureFitUp,
      realityConstrainedSignatureFitFromEventFlow
        (realityConstrainedSignatureFitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A M G P C H Q N =>
      exact
        congrArg some
          (realityConstrainedSignatureFit_mk_congr
            (realityConstrainedSignatureFitDecode_encode_bhist S)
            (realityConstrainedSignatureFitDecode_encode_bhist A)
            (realityConstrainedSignatureFitDecode_encode_bhist M)
            (realityConstrainedSignatureFitDecode_encode_bhist G)
            (realityConstrainedSignatureFitDecode_encode_bhist P)
            (realityConstrainedSignatureFitDecode_encode_bhist C)
            (realityConstrainedSignatureFitDecode_encode_bhist H)
            (realityConstrainedSignatureFitDecode_encode_bhist Q)
            (realityConstrainedSignatureFitDecode_encode_bhist N))

private theorem realityConstrainedSignatureFitToEventFlow_injective
    {x y : RealityConstrainedSignatureFitUp} :
    realityConstrainedSignatureFitToEventFlow x =
      realityConstrainedSignatureFitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realityConstrainedSignatureFitFromEventFlow
          (realityConstrainedSignatureFitToEventFlow x) =
        realityConstrainedSignatureFitFromEventFlow
          (realityConstrainedSignatureFitToEventFlow y) :=
    congrArg realityConstrainedSignatureFitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (realityConstrainedSignatureFit_round_trip x).symm
      (Eq.trans hread (realityConstrainedSignatureFit_round_trip y)))

private theorem realityConstrainedSignatureFit_field_faithful :
    ∀ x y : RealityConstrainedSignatureFitUp,
      realityConstrainedSignatureFitFields x =
        realityConstrainedSignatureFitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S A M G P C H Q N =>
      cases y with
      | mk S' A' M' G' P' C' H' Q' N' =>
          cases hfields
          rfl

instance realityConstrainedSignatureFitBHistCarrier :
    BHistCarrier RealityConstrainedSignatureFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realityConstrainedSignatureFitToEventFlow
  fromEventFlow := realityConstrainedSignatureFitFromEventFlow

instance realityConstrainedSignatureFitChapterTasteGate :
    ChapterTasteGate RealityConstrainedSignatureFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      realityConstrainedSignatureFitFromEventFlow
        (realityConstrainedSignatureFitToEventFlow x) = some x
    exact realityConstrainedSignatureFit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (realityConstrainedSignatureFitToEventFlow_injective heq)

instance realityConstrainedSignatureFitFieldFaithful :
    FieldFaithful RealityConstrainedSignatureFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := realityConstrainedSignatureFitFields
  field_faithful := realityConstrainedSignatureFit_field_faithful

instance realityConstrainedSignatureFitNontrivial :
    BEDC.Meta.TasteGate.Nontrivial RealityConstrainedSignatureFitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealityConstrainedSignatureFitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealityConstrainedSignatureFitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RealityConstrainedSignatureFitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  realityConstrainedSignatureFitChapterTasteGate

theorem RealityConstrainedSignatureFitTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      realityConstrainedSignatureFitDecodeBHist
        (realityConstrainedSignatureFitEncodeBHist h) = h) ∧
      (∀ x : RealityConstrainedSignatureFitUp,
        realityConstrainedSignatureFitFromEventFlow
          (realityConstrainedSignatureFitToEventFlow x) = some x) ∧
        (∀ x y : RealityConstrainedSignatureFitUp,
          realityConstrainedSignatureFitToEventFlow x =
            realityConstrainedSignatureFitToEventFlow y → x = y) ∧
          realityConstrainedSignatureFitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨realityConstrainedSignatureFitDecode_encode_bhist,
      realityConstrainedSignatureFit_round_trip,
      (fun _ _ heq => realityConstrainedSignatureFitToEventFlow_injective heq),
      rfl⟩

theorem RealityConstrainedSignatureFitCarrier_namecert_obligation_rows
    (R : RealityConstrainedSignatureFitUp) :
    ∃ S A M G P C H Q N : BHist,
      R = RealityConstrainedSignatureFitUp.mk S A M G P C H Q N ∧
        realityConstrainedSignatureFitFromEventFlow
          (realityConstrainedSignatureFitToEventFlow R) = some R ∧
          realityConstrainedSignatureFitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases R with
  | mk S A M G P C H Q N =>
      exact
        ⟨S, A, M, G, P, C, H, Q, N, rfl,
          realityConstrainedSignatureFit_round_trip
            (RealityConstrainedSignatureFitUp.mk S A M G P C H Q N),
          rfl⟩

theorem RealityConstrainedSignatureFitCarrier_no_free_descent
    (R : RealityConstrainedSignatureFitUp) :
    ∃ S A M G P C H Q N : BHist,
      R = RealityConstrainedSignatureFitUp.mk S A M G P C H Q N ∧
        realityConstrainedSignatureFitFromEventFlow
          (realityConstrainedSignatureFitToEventFlow R) = some R ∧
          realityConstrainedSignatureFitEncodeBHist BHist.Empty = ([] : List BMark) ∧
          List.Mem S (realityConstrainedSignatureFitFields R) ∧
          List.Mem G (realityConstrainedSignatureFitFields R) ∧
          List.Mem P (realityConstrainedSignatureFitFields R) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases R with
  | mk S A M G P C H Q N =>
      exact
        ⟨S, A, M, G, P, C, H, Q, N, rfl,
          realityConstrainedSignatureFit_round_trip
            (RealityConstrainedSignatureFitUp.mk S A M G P C H Q N),
          rfl, by
            exact List.Mem.head _,
          by
            exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
          by
            exact
              List.Mem.tail _
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))⟩

theorem RealityConstrainedSignatureFitCarrier_formal_target_surface
    (R : RealityConstrainedSignatureFitUp) :
    ∃ S A M G P C H Q N : BHist,
      R = RealityConstrainedSignatureFitUp.mk S A M G P C H Q N ∧
        realityConstrainedSignatureFitFromEventFlow
          (realityConstrainedSignatureFitToEventFlow R) = some R ∧
          realityConstrainedSignatureFitEncodeBHist BHist.Empty = ([] : List BMark) ∧
          List.Mem S (realityConstrainedSignatureFitFields R) ∧
          List.Mem A (realityConstrainedSignatureFitFields R) ∧
          List.Mem M (realityConstrainedSignatureFitFields R) ∧
          List.Mem G (realityConstrainedSignatureFitFields R) ∧
          List.Mem P (realityConstrainedSignatureFitFields R) ∧
          List.Mem C (realityConstrainedSignatureFitFields R) ∧
          List.Mem H (realityConstrainedSignatureFitFields R) ∧
          List.Mem Q (realityConstrainedSignatureFitFields R) ∧
          List.Mem N (realityConstrainedSignatureFitFields R) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases R with
  | mk S A M G P C H Q N =>
      exact
        ⟨S, A, M, G, P, C, H, Q, N, rfl,
          realityConstrainedSignatureFit_round_trip
            (RealityConstrainedSignatureFitUp.mk S A M G P C H Q N),
          rfl,
          by
            exact List.Mem.head _,
          by
            exact List.Mem.tail _ (List.Mem.head _),
          by
            exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)),
          by
            exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
          by
            exact
              List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
          by
            exact
              List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))),
          by
            exact
              List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))),
          by
            exact
              List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))),
          by
            exact
              List.Mem.tail _
                (List.Mem.tail _
                  (List.Mem.tail _
                    (List.Mem.tail _
                      (List.Mem.tail _
                        (List.Mem.tail _
                          (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))))⟩

theorem RealityConstrainedSignatureFitCarrier_finite_nonescape
    (R : RealityConstrainedSignatureFitUp) {row : BHist} :
    List.Mem row (realityConstrainedSignatureFitFields R) →
      ∃ S A M G P C H Q N : BHist,
        R = RealityConstrainedSignatureFitUp.mk S A M G P C H Q N ∧
          (row = S ∨ row = A ∨ row = M ∨ row = G ∨ row = P ∨ row = C ∨
            row = H ∨ row = Q ∨ row = N) ∧
            realityConstrainedSignatureFitFromEventFlow
              (realityConstrainedSignatureFitToEventFlow R) = some R ∧
              realityConstrainedSignatureFitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hrow
  cases R with
  | mk S A M G P C H Q N =>
      change List.Mem row [S, A, M, G, P, C, H, Q, N] at hrow
      have hrowOr :
          row = S ∨ row = A ∨ row = M ∨ row = G ∨ row = P ∨ row = C ∨
            row = H ∨ row = Q ∨ row = N := by
        cases hrow with
        | head =>
            exact Or.inl rfl
        | tail _ hA =>
            cases hA with
            | head =>
                exact Or.inr (Or.inl rfl)
            | tail _ hM =>
                cases hM with
                | head =>
                    exact Or.inr (Or.inr (Or.inl rfl))
                | tail _ hG =>
                    cases hG with
                    | head =>
                        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                    | tail _ hP =>
                        cases hP with
                        | head =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                        | tail _ hC =>
                            cases hC with
                            | head =>
                                exact Or.inr
                                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                            | tail _ hH =>
                                cases hH with
                                | head =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
                                | tail _ hQ =>
                                    cases hQ with
                                    | head =>
                                        exact Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr (Or.inr (Or.inl rfl)))))))
                                    | tail _ hN =>
                                        cases hN with
                                        | head =>
                                            exact Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr (Or.inr rfl)))))))
                                        | tail _ hnil =>
                                            cases hnil
      exact
        ⟨S, A, M, G, P, C, H, Q, N, rfl, hrowOr,
          realityConstrainedSignatureFit_round_trip
            (RealityConstrainedSignatureFitUp.mk S A M G P C H Q N),
          rfl⟩

theorem RealityConstrainedSignatureFitCarrier_gap_policy_exactness
    (R : RealityConstrainedSignatureFitUp) {row : BHist} :
    List.Mem row (realityConstrainedSignatureFitFields R) →
      ∃ S A M G P C H Q N : BHist,
        R = RealityConstrainedSignatureFitUp.mk S A M G P C H Q N ∧
          List.Mem G (realityConstrainedSignatureFitFields R) ∧
          List.Mem P (realityConstrainedSignatureFitFields R) ∧
          (row = S ∨ row = A ∨ row = M ∨ row = G ∨ row = P ∨ row = C ∨
            row = H ∨ row = Q ∨ row = N) ∧
          realityConstrainedSignatureFitFromEventFlow
            (realityConstrainedSignatureFitToEventFlow R) = some R ∧
          realityConstrainedSignatureFitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hrow
  cases R with
  | mk S A M G P C H Q N =>
      change List.Mem row [S, A, M, G, P, C, H, Q, N] at hrow
      have hrowOr :
          row = S ∨ row = A ∨ row = M ∨ row = G ∨ row = P ∨ row = C ∨
            row = H ∨ row = Q ∨ row = N := by
        cases hrow with
        | head =>
            exact Or.inl rfl
        | tail _ hA =>
            cases hA with
            | head =>
                exact Or.inr (Or.inl rfl)
            | tail _ hM =>
                cases hM with
                | head =>
                    exact Or.inr (Or.inr (Or.inl rfl))
                | tail _ hG =>
                    cases hG with
                    | head =>
                        exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                    | tail _ hP =>
                        cases hP with
                        | head =>
                            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                        | tail _ hC =>
                            cases hC with
                            | head =>
                                exact Or.inr
                                  (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
                            | tail _ hH =>
                                cases hH with
                                | head =>
                                    exact Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
                                | tail _ hQ =>
                                    cases hQ with
                                    | head =>
                                        exact Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr (Or.inr (Or.inl rfl)))))))
                                    | tail _ hN =>
                                        cases hN with
                                        | head =>
                                            exact Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr
                                                    (Or.inr
                                                      (Or.inr
                                                        (Or.inr (Or.inr rfl)))))))
                                        | tail _ hnil =>
                                            cases hnil
      exact
        ⟨S, A, M, G, P, C, H, Q, N, rfl,
          by
            exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))),
          by
            exact
              List.Mem.tail _
                (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))),
          hrowOr,
          realityConstrainedSignatureFit_round_trip
            (RealityConstrainedSignatureFitUp.mk S A M G P C H Q N),
          rfl⟩

end BEDC.Derived.RealityConstrainedSignatureFitUp
