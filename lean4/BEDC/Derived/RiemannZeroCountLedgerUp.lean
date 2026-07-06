import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RiemannZeroCountLedgerUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RiemannZeroCountLedgerUp : Type where
  | mk (T Z U M E H C P N : BHist) (count_unary : UnaryHistory U) :
      RiemannZeroCountLedgerUp

def riemannZeroCountLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: riemannZeroCountLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: riemannZeroCountLedgerEncodeBHist h

def riemannZeroCountLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (riemannZeroCountLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (riemannZeroCountLedgerDecodeBHist tail)

private theorem RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist :
    ∀ h : BHist,
      riemannZeroCountLedgerDecodeBHist (riemannZeroCountLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def riemannZeroCountLedgerDecodeUnaryBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  | [] => BHist.Empty
  | BMark.b0 :: _tail => BHist.Empty
  | BMark.b1 :: tail => BHist.e1 (riemannZeroCountLedgerDecodeUnaryBHist tail)

private theorem RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_unary :
    ∀ w : RawEvent, UnaryHistory (riemannZeroCountLedgerDecodeUnaryBHist w) := by
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  intro w
  induction w with
  | nil =>
      constructor
  | cons m tail ih =>
      cases m with
      | b0 =>
          constructor
      | b1 =>
          exact ih

private theorem RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_unary
    {h : BHist} :
    UnaryHistory h →
      riemannZeroCountLedgerDecodeUnaryBHist (riemannZeroCountLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  intro unaryH
  induction h with
  | Empty =>
      rfl
  | e0 h =>
      cases unaryH
  | e1 h ih =>
      exact congrArg BHist.e1 (ih unaryH)

private theorem RiemannZeroCountLedgerTasteGate_single_carrier_alignment_mk_congr
    {T T' Z Z' U U' M M' E E' H H' C C' P P' N N' : BHist}
    (hT : T' = T)
    (hZ : Z' = Z)
    (hU : U' = U)
    (hM : M' = M)
    (hE : E' = E)
    (hH : H' = H)
    (hC : C' = C)
    (hP : P' = P)
    (hN : N' = N)
    (count_unary' : UnaryHistory U')
    (count_unary : UnaryHistory U) :
    RiemannZeroCountLedgerUp.mk T' Z' U' M' E' H' C' P' N' count_unary' =
      RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary := by
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  cases hT
  cases hZ
  cases hU
  cases hM
  cases hE
  cases hH
  cases hC
  cases hP
  cases hN
  have sameProof : count_unary' = count_unary := Subsingleton.elim count_unary' count_unary
  cases sameProof
  rfl

def riemannZeroCountLedgerFields : RiemannZeroCountLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RiemannZeroCountLedgerUp.mk T Z U M E H C P N _count_unary =>
      [T, Z, U, M, E, H, C, P, N]

def riemannZeroCountLedgerToEventFlow : RiemannZeroCountLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (riemannZeroCountLedgerFields x).map riemannZeroCountLedgerEncodeBHist

def riemannZeroCountLedgerFromEventFlow : EventFlow → Option RiemannZeroCountLedgerUp
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  | [] => none
  | T :: rest0 =>
      match rest0 with
      | [] => none
      | Z :: rest1 =>
          match rest1 with
          | [] => none
          | U :: rest2 =>
              match rest2 with
              | [] => none
              | M :: rest3 =>
                  match rest3 with
                  | [] => none
                  | E :: rest4 =>
                      match rest4 with
                      | [] => none
                      | H :: rest5 =>
                          match rest5 with
                          | [] => none
                          | C :: rest6 =>
                              match rest6 with
                              | [] => none
                              | P :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | N :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          let count := riemannZeroCountLedgerDecodeUnaryBHist U
                                          some
                                            (RiemannZeroCountLedgerUp.mk
                                              (riemannZeroCountLedgerDecodeBHist T)
                                              (riemannZeroCountLedgerDecodeBHist Z)
                                              count
                                              (riemannZeroCountLedgerDecodeBHist M)
                                              (riemannZeroCountLedgerDecodeBHist E)
                                              (riemannZeroCountLedgerDecodeBHist H)
                                              (riemannZeroCountLedgerDecodeBHist C)
                                              (riemannZeroCountLedgerDecodeBHist P)
                                              (riemannZeroCountLedgerDecodeBHist N)
                                              (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_unary
                                                U))
                                      | _ :: _ => none

private theorem RiemannZeroCountLedgerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RiemannZeroCountLedgerUp,
      riemannZeroCountLedgerFromEventFlow (riemannZeroCountLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  intro x
  cases x with
  | mk T Z U M E H C P N count_unary =>
      change
        some
          (RiemannZeroCountLedgerUp.mk
            (riemannZeroCountLedgerDecodeBHist (riemannZeroCountLedgerEncodeBHist T))
            (riemannZeroCountLedgerDecodeBHist (riemannZeroCountLedgerEncodeBHist Z))
            (riemannZeroCountLedgerDecodeUnaryBHist (riemannZeroCountLedgerEncodeBHist U))
            (riemannZeroCountLedgerDecodeBHist (riemannZeroCountLedgerEncodeBHist M))
            (riemannZeroCountLedgerDecodeBHist (riemannZeroCountLedgerEncodeBHist E))
            (riemannZeroCountLedgerDecodeBHist (riemannZeroCountLedgerEncodeBHist H))
            (riemannZeroCountLedgerDecodeBHist (riemannZeroCountLedgerEncodeBHist C))
            (riemannZeroCountLedgerDecodeBHist (riemannZeroCountLedgerEncodeBHist P))
            (riemannZeroCountLedgerDecodeBHist (riemannZeroCountLedgerEncodeBHist N))
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_unary
              (riemannZeroCountLedgerEncodeBHist U))) =
          some (RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary)
      exact
        congrArg some
          (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_mk_congr
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist T)
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist Z)
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_unary
              count_unary)
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist M)
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist E)
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist H)
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist C)
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist P)
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist N)
            (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_unary
              (riemannZeroCountLedgerEncodeBHist U))
            count_unary)

private theorem RiemannZeroCountLedgerTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RiemannZeroCountLedgerUp} :
    riemannZeroCountLedgerToEventFlow x = riemannZeroCountLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  intro heq
  have hread :
      riemannZeroCountLedgerFromEventFlow (riemannZeroCountLedgerToEventFlow x) =
        riemannZeroCountLedgerFromEventFlow (riemannZeroCountLedgerToEventFlow y) :=
    congrArg riemannZeroCountLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_round_trip y)))

instance RiemannZeroCountLedgerTasteGate_single_carrier_alignment_bhistCarrier :
    BHistCarrier RiemannZeroCountLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := riemannZeroCountLedgerToEventFlow
  fromEventFlow := riemannZeroCountLedgerFromEventFlow

instance RiemannZeroCountLedgerTasteGate_single_carrier_alignment_chapterTasteGate :
    ChapterTasteGate RiemannZeroCountLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := RiemannZeroCountLedgerTasteGate_single_carrier_alignment_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (RiemannZeroCountLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem RiemannZeroCountLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, List.Mem BMark.b0 (BMark.b0 :: riemannZeroCountLedgerEncodeBHist h)) ∧
      (∀ h : BHist, riemannZeroCountLedgerDecodeBHist
        (riemannZeroCountLedgerEncodeBHist h) = h) ∧
      (∀ x : RiemannZeroCountLedgerUp,
        riemannZeroCountLedgerFromEventFlow (riemannZeroCountLedgerToEventFlow x) = some x) ∧
      (∀ x y : RiemannZeroCountLedgerUp,
        riemannZeroCountLedgerToEventFlow x = riemannZeroCountLedgerToEventFlow y → x = y) := by
  -- BEDC touchpoint anchor: BHist BMark UnaryHistory
  constructor
  · intro _h
    exact List.Mem.head _
  · constructor
    · exact RiemannZeroCountLedgerTasteGate_single_carrier_alignment_decode_encode_bhist
    · constructor
      · exact RiemannZeroCountLedgerTasteGate_single_carrier_alignment_round_trip
      · intro x y heq
        exact RiemannZeroCountLedgerTasteGate_single_carrier_alignment_toEventFlow_injective heq

theorem RiemannZeroCountLedgerCarrier_namecert_obligations
    (x : RiemannZeroCountLedgerUp) :
    ∃ T Z U M E H C P N : BHist,
      (∃ count_unary : UnaryHistory U,
        x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary) ∧
        hsame T T ∧ UnaryHistory U ∧ Cont H C (append H C) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  cases x with
  | mk T Z U M E H C P N count_unary =>
      exact
        ⟨T, Z, U, M, E, H, C, P, N, ⟨count_unary, rfl⟩, hsame_refl T,
          count_unary, rfl⟩

theorem RiemannZeroCountLedger_window_exhaustion
    (x : RiemannZeroCountLedgerUp) :
    ∃ T Z U M E H C P N : BHist,
      (∃ count_unary : UnaryHistory U,
        x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary) ∧
        UnaryHistory U ∧ Cont H C (append H C) ∧ Cont C P (append C P) ∧
          hsame T T ∧ hsame Z Z ∧ hsame M M ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  cases x with
  | mk T Z U M E H C P N count_unary =>
      exact
        ⟨T, Z, U, M, E, H, C, P, N, ⟨count_unary, rfl⟩, count_unary, rfl, rfl,
          hsame_refl T, hsame_refl Z, hsame_refl M, hsame_refl E⟩

theorem RiemannZeroCountLedgerCarrier_window_exhaustion
    (x : RiemannZeroCountLedgerUp) :
    ∃ T Z U M E H C P N : BHist,
      (∃ count_unary : UnaryHistory U,
        x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary) ∧
        UnaryHistory U ∧ hsame T T ∧ hsame Z Z ∧ hsame U U ∧
          Cont H C (append H C) ∧ hsame (append H C) (append H C) := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  cases x with
  | mk T Z U M E H C P N count_unary =>
      exact
        ⟨T, Z, U, M, E, H, C, P, N, ⟨count_unary, rfl⟩, count_unary,
          hsame_refl T, hsame_refl Z, hsame_refl U, rfl, hsame_refl (append H C)⟩

theorem RiemannZeroCountLedgerCarrier_comparison_error_nonescape
    {T Z U M E H C P N comparisonRead exportRead : BHist}
    (count_unary : UnaryHistory U)
    (m_unary : UnaryHistory M)
    (e_unary : UnaryHistory E)
    (comparisonRoute : Cont M E comparisonRead)
    (exportRoute : Cont comparisonRead U exportRead) :
    ∃ x : RiemannZeroCountLedgerUp,
      x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary ∧
        UnaryHistory comparisonRead ∧
          UnaryHistory exportRead ∧
            Cont M E comparisonRead ∧
              Cont comparisonRead U exportRead ∧ hsame M M ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed m_unary e_unary comparisonRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed comparisonUnary count_unary exportRoute
  exact
    ⟨RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary, rfl,
      comparisonUnary, exportUnary, comparisonRoute, exportRoute,
      hsame_refl M, hsame_refl E⟩

theorem RiemannZeroCountLedgerCarrier_zero_list_count_transport
    {T Z U M E H C P N T' Z' U' filterRead countRead : BHist}
    (count_unary : UnaryHistory U)
    (t_unary : UnaryHistory T)
    (z_unary : UnaryHistory Z)
    (sameHeight : hsame T T')
    (sameZeroList : hsame Z Z')
    (sameCount : hsame U U')
    (filterRoute : Cont T Z filterRead)
    (countRoute : Cont filterRead U countRead) :
    ∃ x : RiemannZeroCountLedgerUp,
      x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary ∧
        UnaryHistory T' ∧ UnaryHistory Z' ∧ UnaryHistory U' ∧
          UnaryHistory filterRead ∧ UnaryHistory countRead ∧
            Cont T Z filterRead ∧ Cont filterRead U countRead ∧ hsame Z Z' ∧
              hsame U U' := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  have transportedHeight : UnaryHistory T' :=
    unary_transport t_unary sameHeight
  have transportedZeroList : UnaryHistory Z' :=
    unary_transport z_unary sameZeroList
  have transportedCount : UnaryHistory U' :=
    unary_transport count_unary sameCount
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed t_unary z_unary filterRoute
  have countReadUnary : UnaryHistory countRead :=
    unary_cont_closed filterUnary count_unary countRoute
  exact
    ⟨RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary, rfl,
      transportedHeight, transportedZeroList, transportedCount, filterUnary, countReadUnary,
      filterRoute, countRoute, sameZeroList, sameCount⟩

theorem RiemannZeroCountLedgerCarrier_height_filter_stability
    {T Z U M E H C P N Tprime filterRead : BHist}
    (count_unary : UnaryHistory U)
    (height_unary : UnaryHistory T)
    (sameHeight : hsame T Tprime)
    (filterRoute : Cont T Z filterRead) :
    ∃ x : RiemannZeroCountLedgerUp,
      x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary ∧
        UnaryHistory Tprime ∧ Cont T Z filterRead ∧ hsame T Tprime ∧ hsame T T := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  have transportedHeight : UnaryHistory Tprime :=
    unary_transport height_unary sameHeight
  exact
    ⟨RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary, rfl,
      transportedHeight, filterRoute, sameHeight, hsame_refl T⟩

theorem RiemannZeroCountLedgerCarrier_formal_target_contract
    {T Z U M E H C P N T' Z' U' filterRead countRead comparisonRead exportRead : BHist}
    (count_unary : UnaryHistory U)
    (t_unary : UnaryHistory T)
    (z_unary : UnaryHistory Z)
    (m_unary : UnaryHistory M)
    (e_unary : UnaryHistory E)
    (sameHeight : hsame T T')
    (sameZeroList : hsame Z Z')
    (sameCount : hsame U U')
    (filterRoute : Cont T Z filterRead)
    (countRoute : Cont filterRead U countRead)
    (comparisonRoute : Cont M E comparisonRead)
    (exportRoute : Cont comparisonRead U exportRead) :
    ∃ x : RiemannZeroCountLedgerUp,
      x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary ∧
        UnaryHistory T' ∧ UnaryHistory Z' ∧ UnaryHistory U' ∧
          UnaryHistory filterRead ∧ UnaryHistory countRead ∧
            UnaryHistory comparisonRead ∧ UnaryHistory exportRead ∧
              Cont T Z filterRead ∧ Cont filterRead U countRead ∧
                Cont M E comparisonRead ∧ Cont comparisonRead U exportRead ∧
                  hsame T T' ∧ hsame Z Z' ∧ hsame U U' ∧ hsame M M ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  have transportedHeight : UnaryHistory T' :=
    unary_transport t_unary sameHeight
  have transportedZeroList : UnaryHistory Z' :=
    unary_transport z_unary sameZeroList
  have transportedCount : UnaryHistory U' :=
    unary_transport count_unary sameCount
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed t_unary z_unary filterRoute
  have countReadUnary : UnaryHistory countRead :=
    unary_cont_closed filterUnary count_unary countRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed m_unary e_unary comparisonRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed comparisonUnary count_unary exportRoute
  exact
    ⟨RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary, rfl,
      transportedHeight, transportedZeroList, transportedCount, filterUnary, countReadUnary,
      comparisonUnary, exportUnary, filterRoute, countRoute, comparisonRoute, exportRoute,
      sameHeight, sameZeroList, sameCount, hsame_refl M, hsame_refl E⟩

theorem RiemannZeroCountLedgerCarrier_obligation_routing
    {T Z U M E H C P N T' Z' U' filterRead countRead comparisonRead exportRead publicRead :
      BHist}
    (count_unary : UnaryHistory U)
    (t_unary : UnaryHistory T)
    (z_unary : UnaryHistory Z)
    (m_unary : UnaryHistory M)
    (e_unary : UnaryHistory E)
    (sameHeight : hsame T T')
    (sameZeroList : hsame Z Z')
    (sameCount : hsame U U')
    (filterRoute : Cont T Z filterRead)
    (countRoute : Cont filterRead U countRead)
    (comparisonRoute : Cont M E comparisonRead)
    (exportRoute : Cont comparisonRead U exportRead)
    (publicRoute : Cont countRead exportRead publicRead) :
    ∃ x : RiemannZeroCountLedgerUp,
      x = RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary ∧
        UnaryHistory publicRead ∧
          Cont T Z filterRead ∧
            Cont filterRead U countRead ∧
              Cont M E comparisonRead ∧
                Cont comparisonRead U exportRead ∧
                  Cont countRead exportRead publicRead ∧
                    hsame T T' ∧
                      hsame Z Z' ∧
                        hsame U U' ∧ hsame M M ∧ hsame E E := by
  -- BEDC touchpoint anchor: BHist hsame Cont UnaryHistory
  have filterUnary : UnaryHistory filterRead :=
    unary_cont_closed t_unary z_unary filterRoute
  have countReadUnary : UnaryHistory countRead :=
    unary_cont_closed filterUnary count_unary countRoute
  have comparisonUnary : UnaryHistory comparisonRead :=
    unary_cont_closed m_unary e_unary comparisonRoute
  have exportUnary : UnaryHistory exportRead :=
    unary_cont_closed comparisonUnary count_unary exportRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed countReadUnary exportUnary publicRoute
  exact
    ⟨RiemannZeroCountLedgerUp.mk T Z U M E H C P N count_unary, rfl,
      publicUnary, filterRoute, countRoute, comparisonRoute, exportRoute, publicRoute,
      sameHeight, sameZeroList, sameCount, hsame_refl M, hsame_refl E⟩

end BEDC.Derived.RiemannZeroCountLedgerUp
