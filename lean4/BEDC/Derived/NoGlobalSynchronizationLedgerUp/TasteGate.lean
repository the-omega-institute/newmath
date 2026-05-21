import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NoGlobalSynchronizationLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NoGlobalSynchronizationLedgerUp : Type where
  | mk (h0 h1 refusal boundary locality invariant consumer transport route provenance
      name : BHist) : NoGlobalSynchronizationLedgerUp
  deriving DecidableEq

def noGlobalSynchronizationLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: noGlobalSynchronizationLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: noGlobalSynchronizationLedgerEncodeBHist h

def noGlobalSynchronizationLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (noGlobalSynchronizationLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (noGlobalSynchronizationLedgerDecodeBHist tail)

private theorem noGlobalSynchronizationLedgerDecode_encode_bhist :
    ∀ h : BHist,
      noGlobalSynchronizationLedgerDecodeBHist
        (noGlobalSynchronizationLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def noGlobalSynchronizationLedgerToEventFlow :
    NoGlobalSynchronizationLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NoGlobalSynchronizationLedgerUp.mk h0 h1 refusal boundary locality invariant consumer
      transport route provenance name =>
      [[BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist h0,
        [BMark.b1, BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist h1,
        [BMark.b1, BMark.b1, BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist refusal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist boundary,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist locality,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist invariant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist consumer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        noGlobalSynchronizationLedgerEncodeBHist name]

def noGlobalSynchronizationLedgerFromEventFlow :
    EventFlow → Option NoGlobalSynchronizationLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | h0 :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | h1 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | boundary :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | locality :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | invariant :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | consumer :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | transport :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | route :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | provenance :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | name :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (NoGlobalSynchronizationLedgerUp.mk
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist h0)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist h1)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist refusal)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist boundary)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist locality)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist invariant)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist consumer)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist transport)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist route)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist provenance)
                                                                                                  (noGlobalSynchronizationLedgerDecodeBHist name))
                                                                                          | _ :: _ => none

private theorem noGlobalSynchronizationLedger_round_trip :
    ∀ x : NoGlobalSynchronizationLedgerUp,
      noGlobalSynchronizationLedgerFromEventFlow
        (noGlobalSynchronizationLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk h0 h1 refusal boundary locality invariant consumer transport route provenance name =>
      change
        some
          (NoGlobalSynchronizationLedgerUp.mk
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist h0))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist h1))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist refusal))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist boundary))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist locality))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist invariant))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist consumer))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist transport))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist route))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist provenance))
            (noGlobalSynchronizationLedgerDecodeBHist
              (noGlobalSynchronizationLedgerEncodeBHist name))) =
          some
            (NoGlobalSynchronizationLedgerUp.mk h0 h1 refusal boundary locality invariant
              consumer transport route provenance name)
      rw [noGlobalSynchronizationLedgerDecode_encode_bhist h0,
        noGlobalSynchronizationLedgerDecode_encode_bhist h1,
        noGlobalSynchronizationLedgerDecode_encode_bhist refusal,
        noGlobalSynchronizationLedgerDecode_encode_bhist boundary,
        noGlobalSynchronizationLedgerDecode_encode_bhist locality,
        noGlobalSynchronizationLedgerDecode_encode_bhist invariant,
        noGlobalSynchronizationLedgerDecode_encode_bhist consumer,
        noGlobalSynchronizationLedgerDecode_encode_bhist transport,
        noGlobalSynchronizationLedgerDecode_encode_bhist route,
        noGlobalSynchronizationLedgerDecode_encode_bhist provenance,
        noGlobalSynchronizationLedgerDecode_encode_bhist name]

private theorem noGlobalSynchronizationLedgerToEventFlow_injective
    {x y : NoGlobalSynchronizationLedgerUp} :
    noGlobalSynchronizationLedgerToEventFlow x =
      noGlobalSynchronizationLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      noGlobalSynchronizationLedgerFromEventFlow
          (noGlobalSynchronizationLedgerToEventFlow x) =
        noGlobalSynchronizationLedgerFromEventFlow
          (noGlobalSynchronizationLedgerToEventFlow y) :=
    congrArg noGlobalSynchronizationLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (noGlobalSynchronizationLedger_round_trip x).symm
      (Eq.trans hread (noGlobalSynchronizationLedger_round_trip y)))

instance noGlobalSynchronizationLedgerBHistCarrier :
    BHistCarrier NoGlobalSynchronizationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := noGlobalSynchronizationLedgerToEventFlow
  fromEventFlow := noGlobalSynchronizationLedgerFromEventFlow

instance noGlobalSynchronizationLedgerChapterTasteGate :
    ChapterTasteGate NoGlobalSynchronizationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      noGlobalSynchronizationLedgerFromEventFlow
        (noGlobalSynchronizationLedgerToEventFlow x) = some x
    exact noGlobalSynchronizationLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (noGlobalSynchronizationLedgerToEventFlow_injective heq)

instance noGlobalSynchronizationLedgerFieldFaithful :
    FieldFaithful NoGlobalSynchronizationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | NoGlobalSynchronizationLedgerUp.mk h0 h1 refusal boundary locality invariant consumer
        transport route provenance name =>
        [h0, h1, refusal, boundary, locality, invariant, consumer, transport, route,
          provenance, name]
  field_faithful := by
    -- BEDC touchpoint anchor: BHist BMark
    intro x y h
    cases x with
    | mk h0₁ h1₁ refusal₁ boundary₁ locality₁ invariant₁ consumer₁ transport₁ route₁
        provenance₁ name₁ =>
        cases y with
        | mk h0₂ h1₂ refusal₂ boundary₂ locality₂ invariant₂ consumer₂ transport₂ route₂
            provenance₂ name₂ =>
            cases h
            rfl

instance noGlobalSynchronizationLedgerNontrivial :
    Nontrivial NoGlobalSynchronizationLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NoGlobalSynchronizationLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NoGlobalSynchronizationLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem NoGlobalSynchronizationLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      noGlobalSynchronizationLedgerDecodeBHist
        (noGlobalSynchronizationLedgerEncodeBHist h) = h) ∧
      (∀ x : NoGlobalSynchronizationLedgerUp,
        noGlobalSynchronizationLedgerFromEventFlow
          (noGlobalSynchronizationLedgerToEventFlow x) = some x) ∧
        (∀ x y : NoGlobalSynchronizationLedgerUp,
          noGlobalSynchronizationLedgerToEventFlow x =
            noGlobalSynchronizationLedgerToEventFlow y → x = y) ∧
          noGlobalSynchronizationLedgerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · exact noGlobalSynchronizationLedger_round_trip
    · constructor
      · intro x y heq
        exact noGlobalSynchronizationLedgerToEventFlow_injective heq
      · rfl

theorem NoGlobalSynchronizationLedgerUp_inter_hist_handoff
    {H0 H1 R B O I K S C P N H0' H1' R' B' O' I' K' S' C' P' N'
      localRead consumerRead : BHist}
    (heq :
      noGlobalSynchronizationLedgerToEventFlow
          (NoGlobalSynchronizationLedgerUp.mk H0 H1 R B O I K S C P N) =
        noGlobalSynchronizationLedgerToEventFlow
          (NoGlobalSynchronizationLedgerUp.mk H0' H1' R' B' O' I' K' S' C' P' N'))
    (hlocal : Cont H0 H1 localRead)
    (hconsumer : Cont localRead R consumerRead) :
    Cont H0' H1' localRead ∧ Cont localRead R' consumerRead ∧
      hsame R R' ∧ hsame B B' ∧ hsame K K' := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  have hmk :=
    noGlobalSynchronizationLedgerToEventFlow_injective
      (x := NoGlobalSynchronizationLedgerUp.mk H0 H1 R B O I K S C P N)
      (y := NoGlobalSynchronizationLedgerUp.mk H0' H1' R' B' O' I' K' S' C' P' N')
      heq
  injection hmk with hH0 hH1 hR hB _hO _hI hK _hS _hC _hP _hN
  cases hH0
  cases hH1
  cases hR
  cases hB
  cases hK
  exact ⟨hlocal, hconsumer, hsame_refl R, hsame_refl B, hsame_refl K⟩

end BEDC.Derived.NoGlobalSynchronizationLedgerUp
