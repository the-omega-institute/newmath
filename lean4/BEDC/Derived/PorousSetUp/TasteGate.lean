import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PorousSetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PorousSetUp : Type where
  | mk (M L R E H W D S T C Q N : BHist) : PorousSetUp
  deriving DecidableEq

def porousSetFields : PorousSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PorousSetUp.mk M L R E H W D S T C Q N => [M, L, R, E, H, W, D, S, T, C, Q, N]

def porousSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: porousSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: porousSetEncodeBHist h

def porousSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (porousSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (porousSetDecodeBHist tail)

private theorem porousSetDecode_encode_bhist :
    ∀ h : BHist, porousSetDecodeBHist (porousSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem porousSet_mk_congr
    {M M' L L' R R' E E' H H' W W' D D' S S' T T' C C' Q Q' N N' : BHist}
    (hM : M' = M) (hL : L' = L) (hR : R' = R) (hE : E' = E)
    (hH : H' = H) (hW : W' = W) (hD : D' = D) (hS : S' = S)
    (hT : T' = T) (hC : C' = C) (hQ : Q' = Q) (hN : N' = N) :
    PorousSetUp.mk M' L' R' E' H' W' D' S' T' C' Q' N' =
      PorousSetUp.mk M L R E H W D S T C Q N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hM
  cases hL
  cases hR
  cases hE
  cases hH
  cases hW
  cases hD
  cases hS
  cases hT
  cases hC
  cases hQ
  cases hN
  rfl

def porousSetToEventFlow : PorousSetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PorousSetUp.mk M L R E H W D S T C Q N =>
      [[BMark.b0],
        porousSetEncodeBHist M,
        [BMark.b1, BMark.b0],
        porousSetEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b0],
        porousSetEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        porousSetEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        porousSetEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        porousSetEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        porousSetEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        porousSetEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        porousSetEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        porousSetEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        porousSetEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        porousSetEncodeBHist N]

def porousSetFromEventFlow : EventFlow → Option PorousSetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | M :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | L :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | R :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | E :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | H :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | W :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | D :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | S :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | T :: rest17 =>
                                                                          match rest17
                                                                            with
                                                                          | [] => none
                                                                          | _tag9 ::
                                                                              rest18 =>
                                                                              match
                                                                                rest18
                                                                              with
                                                                              | [] =>
                                                                                  none
                                                                              | C ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | Q ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | N ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (PorousSetUp.mk
                                                                                                          (porousSetDecodeBHist
                                                                                                            M)
                                                                                                          (porousSetDecodeBHist
                                                                                                            L)
                                                                                                          (porousSetDecodeBHist
                                                                                                            R)
                                                                                                          (porousSetDecodeBHist
                                                                                                            E)
                                                                                                          (porousSetDecodeBHist
                                                                                                            H)
                                                                                                          (porousSetDecodeBHist
                                                                                                            W)
                                                                                                          (porousSetDecodeBHist
                                                                                                            D)
                                                                                                          (porousSetDecodeBHist
                                                                                                            S)
                                                                                                          (porousSetDecodeBHist
                                                                                                            T)
                                                                                                          (porousSetDecodeBHist
                                                                                                            C)
                                                                                                          (porousSetDecodeBHist
                                                                                                            Q)
                                                                                                          (porousSetDecodeBHist
                                                                                                            N))
                                                                                                  | _ :: _ =>
                                                                                                      none

private theorem porousSet_round_trip :
    ∀ x : PorousSetUp, porousSetFromEventFlow (porousSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk M L R E H W D S T C Q N =>
      change
        some
            (PorousSetUp.mk
              (porousSetDecodeBHist (porousSetEncodeBHist M))
              (porousSetDecodeBHist (porousSetEncodeBHist L))
              (porousSetDecodeBHist (porousSetEncodeBHist R))
              (porousSetDecodeBHist (porousSetEncodeBHist E))
              (porousSetDecodeBHist (porousSetEncodeBHist H))
              (porousSetDecodeBHist (porousSetEncodeBHist W))
              (porousSetDecodeBHist (porousSetEncodeBHist D))
              (porousSetDecodeBHist (porousSetEncodeBHist S))
              (porousSetDecodeBHist (porousSetEncodeBHist T))
              (porousSetDecodeBHist (porousSetEncodeBHist C))
              (porousSetDecodeBHist (porousSetEncodeBHist Q))
              (porousSetDecodeBHist (porousSetEncodeBHist N))) =
          some (PorousSetUp.mk M L R E H W D S T C Q N)
      exact
        congrArg some
          (porousSet_mk_congr
            (porousSetDecode_encode_bhist M)
            (porousSetDecode_encode_bhist L)
            (porousSetDecode_encode_bhist R)
            (porousSetDecode_encode_bhist E)
            (porousSetDecode_encode_bhist H)
            (porousSetDecode_encode_bhist W)
            (porousSetDecode_encode_bhist D)
            (porousSetDecode_encode_bhist S)
            (porousSetDecode_encode_bhist T)
            (porousSetDecode_encode_bhist C)
            (porousSetDecode_encode_bhist Q)
            (porousSetDecode_encode_bhist N))

private theorem porousSetToEventFlow_injective {x y : PorousSetUp} :
    porousSetToEventFlow x = porousSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk M1 L1 R1 E1 H1 W1 D1 S1 T1 C1 Q1 N1 =>
      cases y with
      | mk M2 L2 R2 E2 H2 W2 D2 S2 T2 C2 Q2 N2 =>
          injection heq with _ hTail1
          injection hTail1 with hM hTail2
          injection hTail2 with _ hTail3
          injection hTail3 with hL hTail4
          injection hTail4 with _ hTail5
          injection hTail5 with hR hTail6
          injection hTail6 with _ hTail7
          injection hTail7 with hE hTail8
          injection hTail8 with _ hTail9
          injection hTail9 with hH hTail10
          injection hTail10 with _ hTail11
          injection hTail11 with hW hTail12
          injection hTail12 with _ hTail13
          injection hTail13 with hD hTail14
          injection hTail14 with _ hTail15
          injection hTail15 with hS hTail16
          injection hTail16 with _ hTail17
          injection hTail17 with hT hTail18
          injection hTail18 with _ hTail19
          injection hTail19 with hC hTail20
          injection hTail20 with _ hTail21
          injection hTail21 with hQ hTail22
          injection hTail22 with _ hTail23
          injection hTail23 with hN _
          have hm : M1 = M2 := by
            exact Eq.trans (porousSetDecode_encode_bhist M1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hM)
                (porousSetDecode_encode_bhist M2))
          have hl : L1 = L2 := by
            exact Eq.trans (porousSetDecode_encode_bhist L1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hL)
                (porousSetDecode_encode_bhist L2))
          have hr : R1 = R2 := by
            exact Eq.trans (porousSetDecode_encode_bhist R1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hR)
                (porousSetDecode_encode_bhist R2))
          have he : E1 = E2 := by
            exact Eq.trans (porousSetDecode_encode_bhist E1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hE)
                (porousSetDecode_encode_bhist E2))
          have hh : H1 = H2 := by
            exact Eq.trans (porousSetDecode_encode_bhist H1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hH)
                (porousSetDecode_encode_bhist H2))
          have hw : W1 = W2 := by
            exact Eq.trans (porousSetDecode_encode_bhist W1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hW)
                (porousSetDecode_encode_bhist W2))
          have hd : D1 = D2 := by
            exact Eq.trans (porousSetDecode_encode_bhist D1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hD)
                (porousSetDecode_encode_bhist D2))
          have hs : S1 = S2 := by
            exact Eq.trans (porousSetDecode_encode_bhist S1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hS)
                (porousSetDecode_encode_bhist S2))
          have ht : T1 = T2 := by
            exact Eq.trans (porousSetDecode_encode_bhist T1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hT)
                (porousSetDecode_encode_bhist T2))
          have hc : C1 = C2 := by
            exact Eq.trans (porousSetDecode_encode_bhist C1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hC)
                (porousSetDecode_encode_bhist C2))
          have hq : Q1 = Q2 := by
            exact Eq.trans (porousSetDecode_encode_bhist Q1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hQ)
                (porousSetDecode_encode_bhist Q2))
          have hn : N1 = N2 := by
            exact Eq.trans (porousSetDecode_encode_bhist N1).symm
              (Eq.trans (congrArg porousSetDecodeBHist hN)
                (porousSetDecode_encode_bhist N2))
          cases hm
          cases hl
          cases hr
          cases he
          cases hh
          cases hw
          cases hd
          cases hs
          cases ht
          cases hc
          cases hq
          cases hn
          rfl

instance porousSetBHistCarrier : BHistCarrier PorousSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := porousSetToEventFlow
  fromEventFlow := porousSetFromEventFlow

instance porousSetChapterTasteGate : ChapterTasteGate PorousSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change porousSetFromEventFlow (porousSetToEventFlow x) = some x
    exact porousSet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (porousSetToEventFlow_injective heq)

instance porousSetFieldFaithful : FieldFaithful PorousSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := porousSetFields
  field_faithful := by
    intro x y h
    exact porousSetToEventFlow_injective (by
      cases x with
      | mk M1 L1 R1 E1 H1 W1 D1 S1 T1 C1 Q1 N1 =>
          cases y with
          | mk M2 L2 R2 E2 H2 W2 D2 S2 T2 C2 Q2 N2 =>
              simp only [porousSetFields] at h
              injection h with hM t1
              injection t1 with hL t2
              injection t2 with hR t3
              injection t3 with hE t4
              injection t4 with hH t5
              injection t5 with hW t6
              injection t6 with hD t7
              injection t7 with hS t8
              injection t8 with hT t9
              injection t9 with hC t10
              injection t10 with hQ t11
              injection t11 with hN _
              cases hM
              cases hL
              cases hR
              cases hE
              cases hH
              cases hW
              cases hD
              cases hS
              cases hT
              cases hC
              cases hQ
              cases hN
              rfl)

instance porousSetNontrivial : Nontrivial PorousSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PorousSetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PorousSetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem PorousSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, porousSetDecodeBHist (porousSetEncodeBHist h) = h) ∧
      (∀ x : PorousSetUp, porousSetFromEventFlow (porousSetToEventFlow x) = some x) ∧
        (∀ x y : PorousSetUp, porousSetToEventFlow x = porousSetToEventFlow y → x = y) ∧
          porousSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    And.intro porousSetDecode_encode_bhist
      (And.intro porousSet_round_trip
        (And.intro (fun x y heq => porousSetToEventFlow_injective heq) rfl))

end BEDC.Derived.PorousSetUp.TasteGate
