import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObservationTimeOrderUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObservationTimeOrderUp : Type where
  | mk :
      (earlier later retained route gap transports provenance nameCert : BHist) →
      ObservationTimeOrderUp
  deriving DecidableEq

def observationTimeOrderEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observationTimeOrderEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observationTimeOrderEncodeBHist h

def observationTimeOrderDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observationTimeOrderDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observationTimeOrderDecodeBHist tail)

private theorem observationTimeOrderDecode_encode_bhist :
    ∀ h : BHist, observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observationTimeOrderToEventFlow : ObservationTimeOrderUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationTimeOrderUp.mk earlier later retained route gap transports provenance nameCert =>
      [[BMark.b0],
        observationTimeOrderEncodeBHist earlier,
        [BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist later,
        [BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist retained,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observationTimeOrderEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observationTimeOrderEncodeBHist nameCert]

def observationTimeOrderFromEventFlow : EventFlow → Option ObservationTimeOrderUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | earlier :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | later :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | retained :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | gap :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | nameCert :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (ObservationTimeOrderUp.mk
                                                                          (observationTimeOrderDecodeBHist
                                                                            earlier)
                                                                          (observationTimeOrderDecodeBHist
                                                                            later)
                                                                          (observationTimeOrderDecodeBHist
                                                                            retained)
                                                                          (observationTimeOrderDecodeBHist
                                                                            route)
                                                                          (observationTimeOrderDecodeBHist
                                                                            gap)
                                                                          (observationTimeOrderDecodeBHist
                                                                            transports)
                                                                          (observationTimeOrderDecodeBHist
                                                                            provenance)
                                                                          (observationTimeOrderDecodeBHist
                                                                            nameCert))
                                                                  | _ :: _ => none

private theorem observationTimeOrder_round_trip :
    ∀ x : ObservationTimeOrderUp,
      observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk earlier later retained route gap transports provenance nameCert =>
      change
        some
          (ObservationTimeOrderUp.mk
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist earlier))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist later))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist retained))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist route))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist gap))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist transports))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist provenance))
            (observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist nameCert))) =
          some
            (ObservationTimeOrderUp.mk earlier later retained route gap transports provenance
              nameCert)
      rw [observationTimeOrderDecode_encode_bhist earlier,
        observationTimeOrderDecode_encode_bhist later,
        observationTimeOrderDecode_encode_bhist retained,
        observationTimeOrderDecode_encode_bhist route,
        observationTimeOrderDecode_encode_bhist gap,
        observationTimeOrderDecode_encode_bhist transports,
        observationTimeOrderDecode_encode_bhist provenance,
        observationTimeOrderDecode_encode_bhist nameCert]

private theorem observationTimeOrderToEventFlow_injective {x y : ObservationTimeOrderUp} :
    observationTimeOrderToEventFlow x = observationTimeOrderToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow x) =
        observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow y) :=
    congrArg observationTimeOrderFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observationTimeOrder_round_trip x).symm
      (Eq.trans hread (observationTimeOrder_round_trip y)))

instance observationTimeOrderBHistCarrier : BHistCarrier ObservationTimeOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observationTimeOrderToEventFlow
  fromEventFlow := observationTimeOrderFromEventFlow

instance observationTimeOrderChapterTasteGate : ChapterTasteGate ObservationTimeOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow x) = some x
    exact observationTimeOrder_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observationTimeOrderToEventFlow_injective heq)

def observationTimeOrderFields : ObservationTimeOrderUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ObservationTimeOrderUp.mk O0 O1 R C G H P N => [O0, O1, R, C, G, H, P, N]

theorem observationTimeOrderFields_faithful :
    ∀ x y : ObservationTimeOrderUp, observationTimeOrderFields x = observationTimeOrderFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  intro x y h
  cases x with
  | mk O0₁ O1₁ R₁ C₁ G₁ H₁ P₁ N₁ =>
      cases y with
      | mk O0₂ O1₂ R₂ C₂ G₂ H₂ P₂ N₂ =>
          injection h with hO0 tail0
          injection tail0 with hO1 tail1
          injection tail1 with hR tail2
          injection tail2 with hC tail3
          injection tail3 with hG tail4
          injection tail4 with hH tail5
          injection tail5 with hP tail6
          injection tail6 with hN _nil
          subst hO0
          subst hO1
          subst hR
          subst hC
          subst hG
          subst hH
          subst hP
          subst hN
          rfl

instance observationTimeOrderFieldFaithful : FieldFaithful ObservationTimeOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := observationTimeOrderFields
  field_faithful := observationTimeOrderFields_faithful

instance observationTimeOrderNontrivial : Nontrivial ObservationTimeOrderUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObservationTimeOrderUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      ObservationTimeOrderUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ObservationTimeOrderTasteGate_single_carrier_alignment :
    (∀ h : BHist, observationTimeOrderDecodeBHist (observationTimeOrderEncodeBHist h) = h) ∧
      (∀ x : ObservationTimeOrderUp,
        observationTimeOrderFromEventFlow (observationTimeOrderToEventFlow x) = some x) ∧
        (∀ x y : ObservationTimeOrderUp,
          observationTimeOrderToEventFlow x = observationTimeOrderToEventFlow y → x = y) ∧
          observationTimeOrderEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact observationTimeOrderDecode_encode_bhist
  · constructor
    · exact observationTimeOrder_round_trip
    · constructor
      · intro x y heq
        exact observationTimeOrderToEventFlow_injective heq
      · rfl

theorem ObservationTimeOrderRetainedRecord_exactness
    {O0 O1 R C G H P N sourceRead targetRead classifierRead : BHist} :
    UnaryHistory O0 →
      UnaryHistory O1 →
        UnaryHistory R →
          UnaryHistory C →
            Cont O0 O1 sourceRead →
              Cont sourceRead R targetRead →
                Cont targetRead C classifierRead →
                  observationTimeOrderFromEventFlow
                      (observationTimeOrderToEventFlow
                        (ObservationTimeOrderUp.mk O0 O1 R C G H P N)) =
                    some (ObservationTimeOrderUp.mk O0 O1 R C G H P N) →
                    UnaryHistory sourceRead ∧
                      UnaryHistory targetRead ∧
                        UnaryHistory classifierRead ∧
                          hsame
                            (observationTimeOrderDecodeBHist
                              (observationTimeOrderEncodeBHist R))
                            R := by
  -- BEDC touchpoint anchor: BHist hsame Cont ChapterTasteGate
  intro sourceUnary targetUnary retainedUnary routeUnary sourceRoute targetRoute classifierRoute
    _readback
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary targetUnary sourceRoute
  have targetReadUnary : UnaryHistory targetRead :=
    unary_cont_closed sourceReadUnary retainedUnary targetRoute
  have classifierReadUnary : UnaryHistory classifierRead :=
    unary_cont_closed targetReadUnary routeUnary classifierRoute
  exact
    ⟨sourceReadUnary,
      targetReadUnary,
      classifierReadUnary,
      observationTimeOrderDecode_encode_bhist R⟩

theorem ObservationTimeOrderErasureBoundary_gap_route
    {O0 O1 R C G H P N recordRead retainedRead gapRead : BHist} :
    UnaryHistory O0 →
      UnaryHistory O1 →
        UnaryHistory R →
          UnaryHistory G →
            Cont O0 O1 recordRead →
              Cont recordRead R retainedRead →
                Cont retainedRead G gapRead →
                  observationTimeOrderFromEventFlow
                      (observationTimeOrderToEventFlow
                        (ObservationTimeOrderUp.mk O0 O1 R C G H P N)) =
                    some (ObservationTimeOrderUp.mk O0 O1 R C G H P N) →
                    UnaryHistory recordRead ∧
                      UnaryHistory retainedRead ∧
                        UnaryHistory gapRead ∧
                          hsame
                            (observationTimeOrderDecodeBHist
                              (observationTimeOrderEncodeBHist G))
                            G := by
  -- BEDC touchpoint anchor: BHist hsame Cont ChapterTasteGate
  intro sourceUnary targetUnary retainedUnary gapUnary sourceRoute targetRoute gapRoute
    _readback
  have recordReadUnary : UnaryHistory recordRead :=
    unary_cont_closed sourceUnary targetUnary sourceRoute
  have retainedReadUnary : UnaryHistory retainedRead :=
    unary_cont_closed recordReadUnary retainedUnary targetRoute
  have gapReadUnary : UnaryHistory gapRead :=
    unary_cont_closed retainedReadUnary gapUnary gapRoute
  exact
    ⟨recordReadUnary,
      retainedReadUnary,
      gapReadUnary,
      observationTimeOrderDecode_encode_bhist G⟩

theorem ObservationTimeOrderNo_host_time_nonescape (O0 O1 R C G H P N : BHist) :
    NameCert
        (fun h : BHist =>
          hsame h O0 ∨ hsame h O1 ∨ hsame h R ∨ hsame h C ∨ hsame h G ∨
            hsame h H ∨ hsame h P ∨ hsame h N)
        hsame ∧
      observationTimeOrderFields (ObservationTimeOrderUp.mk O0 O1 R C G H P N) =
        [O0, O1, R, C, G, H, P, N] := by
  -- BEDC touchpoint anchor: BHist hsame NameCert
  constructor
  · exact {
      carrier_inhabited := Exists.intro O0 (Or.inl (hsame_refl O0))
      equiv_refl := by
        intro h _carrier
        exact hsame_refl h
      equiv_symm := by
        intro _h _k sameHK
        exact hsame_symm sameHK
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK carrierH
        have sameKH : hsame k h := hsame_symm sameHK
        cases carrierH with
        | inl sameO0 =>
            exact Or.inl (hsame_trans sameKH sameO0)
        | inr rest =>
            cases rest with
            | inl sameO1 =>
                exact Or.inr (Or.inl (hsame_trans sameKH sameO1))
            | inr rest =>
                cases rest with
                | inl sameR =>
                    exact Or.inr (Or.inr (Or.inl (hsame_trans sameKH sameR)))
                | inr rest =>
                    cases rest with
                    | inl sameC =>
                        exact Or.inr (Or.inr (Or.inr (Or.inl (hsame_trans sameKH sameC))))
                    | inr rest =>
                        cases rest with
                        | inl sameG =>
                            exact
                              Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr (Or.inl (hsame_trans sameKH sameG)))))
                        | inr rest =>
                            cases rest with
                            | inl sameH =>
                                exact
                                  Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr (Or.inl (hsame_trans sameKH sameH))))))
                            | inr rest =>
                                cases rest with
                                | inl sameP =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inl (hsame_trans sameKH sameP)))))))
                                | inr sameN =>
                                    exact
                                      Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (Or.inr
                                                (Or.inr
                                                  (Or.inr (hsame_trans sameKH sameN)))))))
    }
  · rfl

end BEDC.Derived.ObservationTimeOrderUp
