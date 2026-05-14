import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ObserverBoundarySelectorUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ObserverBoundarySelectorUp : Type where
  | mk :
      (source selected omitted decision transport ledger route provenance nameCert : BHist) →
      ObserverBoundarySelectorUp

def observerBoundarySelectorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: observerBoundarySelectorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: observerBoundarySelectorEncodeBHist h

def observerBoundarySelectorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (observerBoundarySelectorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (observerBoundarySelectorDecodeBHist tail)

private theorem observerBoundarySelectorDecode_encode_bhist :
    ∀ h : BHist,
      observerBoundarySelectorDecodeBHist (observerBoundarySelectorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def observerBoundarySelectorToEventFlow : ObserverBoundarySelectorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ObserverBoundarySelectorUp.mk source selected omitted decision transport ledger route
      provenance nameCert =>
      [[BMark.b0],
        observerBoundarySelectorEncodeBHist source,
        [BMark.b1, BMark.b0],
        observerBoundarySelectorEncodeBHist selected,
        [BMark.b1, BMark.b1, BMark.b0],
        observerBoundarySelectorEncodeBHist omitted,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBoundarySelectorEncodeBHist decision,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBoundarySelectorEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBoundarySelectorEncodeBHist ledger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        observerBoundarySelectorEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        observerBoundarySelectorEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        observerBoundarySelectorEncodeBHist nameCert]

private def observerBoundarySelectorDecodeEventRows : Nat → EventFlow → Option (List RawEvent)
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => some []
  | Nat.zero, _ :: _ => none
  | Nat.succ _, [] => none
  | Nat.succ n, _tag :: rest0 =>
      match rest0 with
      | [] => none
      | row :: rest1 =>
          match observerBoundarySelectorDecodeEventRows n rest1 with
          | none => none
          | some rows => some (row :: rows)

def observerBoundarySelectorFromEventFlow : EventFlow → Option ObserverBoundarySelectorUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      match observerBoundarySelectorDecodeEventRows 9 ef with
      | none => none
      | some rows =>
          match rows with
          | [] => none
          | source :: rest0 =>
              match rest0 with
              | [] => none
              | selected :: rest1 =>
                  match rest1 with
                  | [] => none
                  | omitted :: rest2 =>
                      match rest2 with
                      | [] => none
                      | decision :: rest3 =>
                          match rest3 with
                          | [] => none
                          | transport :: rest4 =>
                              match rest4 with
                              | [] => none
                              | ledger :: rest5 =>
                                  match rest5 with
                                  | [] => none
                                  | route :: rest6 =>
                                      match rest6 with
                                      | [] => none
                                      | provenance :: rest7 =>
                                          match rest7 with
                                          | [] => none
                                          | nameCert :: rest8 =>
                                              match rest8 with
                                              | [] =>
                                                  some
                                                    (ObserverBoundarySelectorUp.mk
                                                      (observerBoundarySelectorDecodeBHist source)
                                                      (observerBoundarySelectorDecodeBHist selected)
                                                      (observerBoundarySelectorDecodeBHist omitted)
                                                      (observerBoundarySelectorDecodeBHist decision)
                                                      (observerBoundarySelectorDecodeBHist transport)
                                                      (observerBoundarySelectorDecodeBHist ledger)
                                                      (observerBoundarySelectorDecodeBHist route)
                                                      (observerBoundarySelectorDecodeBHist provenance)
                                                      (observerBoundarySelectorDecodeBHist nameCert))
                                              | _ :: _ => none

private theorem observerBoundarySelector_round_trip :
    ∀ x : ObserverBoundarySelectorUp,
      observerBoundarySelectorFromEventFlow (observerBoundarySelectorToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source selected omitted decision transport ledger route provenance nameCert =>
      change
        some
          (ObserverBoundarySelectorUp.mk
            (observerBoundarySelectorDecodeBHist (observerBoundarySelectorEncodeBHist source))
            (observerBoundarySelectorDecodeBHist
              (observerBoundarySelectorEncodeBHist selected))
            (observerBoundarySelectorDecodeBHist (observerBoundarySelectorEncodeBHist omitted))
            (observerBoundarySelectorDecodeBHist
              (observerBoundarySelectorEncodeBHist decision))
            (observerBoundarySelectorDecodeBHist
              (observerBoundarySelectorEncodeBHist transport))
            (observerBoundarySelectorDecodeBHist (observerBoundarySelectorEncodeBHist ledger))
            (observerBoundarySelectorDecodeBHist (observerBoundarySelectorEncodeBHist route))
            (observerBoundarySelectorDecodeBHist
              (observerBoundarySelectorEncodeBHist provenance))
            (observerBoundarySelectorDecodeBHist
              (observerBoundarySelectorEncodeBHist nameCert))) =
          some
            (ObserverBoundarySelectorUp.mk source selected omitted decision transport ledger
              route provenance nameCert)
      rw [observerBoundarySelectorDecode_encode_bhist source,
        observerBoundarySelectorDecode_encode_bhist selected,
        observerBoundarySelectorDecode_encode_bhist omitted,
        observerBoundarySelectorDecode_encode_bhist decision,
        observerBoundarySelectorDecode_encode_bhist transport,
        observerBoundarySelectorDecode_encode_bhist ledger,
        observerBoundarySelectorDecode_encode_bhist route,
        observerBoundarySelectorDecode_encode_bhist provenance,
        observerBoundarySelectorDecode_encode_bhist nameCert]

private theorem observerBoundarySelectorToEventFlow_injective
    {x y : ObserverBoundarySelectorUp} :
    observerBoundarySelectorToEventFlow x = observerBoundarySelectorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      observerBoundarySelectorFromEventFlow (observerBoundarySelectorToEventFlow x) =
        observerBoundarySelectorFromEventFlow (observerBoundarySelectorToEventFlow y) :=
    congrArg observerBoundarySelectorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (observerBoundarySelector_round_trip x).symm
      (Eq.trans hread (observerBoundarySelector_round_trip y)))

instance observerBoundarySelectorBHistCarrier :
    BHistCarrier ObserverBoundarySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := observerBoundarySelectorToEventFlow
  fromEventFlow := observerBoundarySelectorFromEventFlow

instance observerBoundarySelectorChapterTasteGate :
    ChapterTasteGate ObserverBoundarySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      observerBoundarySelectorFromEventFlow (observerBoundarySelectorToEventFlow x) =
        some x
    exact observerBoundarySelector_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (observerBoundarySelectorToEventFlow_injective heq)

instance observerBoundarySelectorFieldFaithful :
    FieldFaithful ObserverBoundarySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | ObserverBoundarySelectorUp.mk source selected omitted decision transport ledger route
        provenance nameCert =>
        [source, selected, omitted, decision, transport, ledger, route, provenance, nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk source₁ selected₁ omitted₁ decision₁ transport₁ ledger₁ route₁ provenance₁
        nameCert₁ =>
      cases y with
      | mk source₂ selected₂ omitted₂ decision₂ transport₂ ledger₂ route₂ provenance₂
          nameCert₂ =>
        injection h with hSource t1
        injection t1 with hSelected t2
        injection t2 with hOmitted t3
        injection t3 with hDecision t4
        injection t4 with hTransport t5
        injection t5 with hLedger t6
        injection t6 with hRoute t7
        injection t7 with hProvenance t8
        injection t8 with hNameCert _
        cases hSource
        cases hSelected
        cases hOmitted
        cases hDecision
        cases hTransport
        cases hLedger
        cases hRoute
        cases hProvenance
        cases hNameCert
        rfl

instance observerBoundarySelectorNontrivial :
    Nontrivial ObserverBoundarySelectorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ObserverBoundarySelectorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ObserverBoundarySelectorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ObserverBoundarySelectorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  observerBoundarySelectorChapterTasteGate

theorem ObserverBoundarySelectorTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      observerBoundarySelectorDecodeBHist (observerBoundarySelectorEncodeBHist h) = h) ∧
      (∀ x : ObserverBoundarySelectorUp,
        observerBoundarySelectorFromEventFlow (observerBoundarySelectorToEventFlow x) =
          some x) ∧
        (∀ x y : ObserverBoundarySelectorUp,
          observerBoundarySelectorToEventFlow x = observerBoundarySelectorToEventFlow y →
            x = y) ∧
          Nonempty (FieldFaithful ObserverBoundarySelectorUp) ∧
            Nonempty (Nontrivial ObserverBoundarySelectorUp) ∧
              observerBoundarySelectorEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful
  constructor
  · exact observerBoundarySelectorDecode_encode_bhist
  · constructor
    · exact observerBoundarySelector_round_trip
    · constructor
      · intro x y heq
        exact observerBoundarySelectorToEventFlow_injective heq
      · constructor
        · exact ⟨observerBoundarySelectorFieldFaithful⟩
        · constructor
          · exact ⟨observerBoundarySelectorNontrivial⟩
          · rfl

end BEDC.Derived.ObserverBoundarySelectorUp.TasteGate

namespace BEDC.Derived.ObserverBoundarySelectorUp

def taste_gate :=
  -- BEDC touchpoint anchor: BHist BMark
  TasteGate.taste_gate

end BEDC.Derived.ObserverBoundarySelectorUp
