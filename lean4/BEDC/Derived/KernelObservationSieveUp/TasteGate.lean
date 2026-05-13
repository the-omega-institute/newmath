import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelObservationSieveUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelObservationSieveUp : Type where
  | mk :
      (observer selector filter accepted rejected transport routes provenance
        nameCert : BHist) →
      KernelObservationSieveUp
  deriving DecidableEq

def kernelObservationSieveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelObservationSieveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelObservationSieveEncodeBHist h

def kernelObservationSieveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelObservationSieveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelObservationSieveDecodeBHist tail)

private theorem kernelObservationSieveDecode_encode_bhist :
    ∀ h : BHist,
      kernelObservationSieveDecodeBHist
        (kernelObservationSieveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kernelObservationSieveToEventFlow :
    KernelObservationSieveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelObservationSieveUp.mk observer selector filter accepted rejected transport routes
      provenance nameCert =>
      [[BMark.b0], kernelObservationSieveEncodeBHist observer, [BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist selector, [BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist filter, [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist accepted,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist rejected,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelObservationSieveEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist nameCert]

def kernelObservationSieveFromEventFlow :
    EventFlow → Option KernelObservationSieveUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observer :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | selector :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | filter :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | accepted :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | rejected :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (KernelObservationSieveUp.mk
                                                                                  (kernelObservationSieveDecodeBHist
                                                                                    observer)
                                                                                  (kernelObservationSieveDecodeBHist
                                                                                    selector)
                                                                                  (kernelObservationSieveDecodeBHist
                                                                                    filter)
                                                                                  (kernelObservationSieveDecodeBHist
                                                                                    accepted)
                                                                                  (kernelObservationSieveDecodeBHist
                                                                                    rejected)
                                                                                  (kernelObservationSieveDecodeBHist
                                                                                    transport)
                                                                                  (kernelObservationSieveDecodeBHist
                                                                                    routes)
                                                                                  (kernelObservationSieveDecodeBHist
                                                                                    provenance)
                                                                                  (kernelObservationSieveDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ => none

private theorem kernelObservationSieve_round_trip :
    ∀ x : KernelObservationSieveUp,
      kernelObservationSieveFromEventFlow
        (kernelObservationSieveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observer selector filter accepted rejected transport routes provenance nameCert =>
      change
        some
          (KernelObservationSieveUp.mk
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist observer))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist selector))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist filter))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist accepted))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist rejected))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist transport))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist routes))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist provenance))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist nameCert))) =
          some
            (KernelObservationSieveUp.mk observer selector filter accepted rejected transport
              routes provenance nameCert)
      rw [kernelObservationSieveDecode_encode_bhist observer,
        kernelObservationSieveDecode_encode_bhist selector,
        kernelObservationSieveDecode_encode_bhist filter,
        kernelObservationSieveDecode_encode_bhist accepted,
        kernelObservationSieveDecode_encode_bhist rejected,
        kernelObservationSieveDecode_encode_bhist transport,
        kernelObservationSieveDecode_encode_bhist routes,
        kernelObservationSieveDecode_encode_bhist provenance,
        kernelObservationSieveDecode_encode_bhist nameCert]

private theorem kernelObservationSieveToEventFlow_injective
    {x y : KernelObservationSieveUp} :
    kernelObservationSieveToEventFlow x =
      kernelObservationSieveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelObservationSieveFromEventFlow
          (kernelObservationSieveToEventFlow x) =
        kernelObservationSieveFromEventFlow
          (kernelObservationSieveToEventFlow y) :=
    congrArg kernelObservationSieveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelObservationSieve_round_trip x).symm
      (Eq.trans hread (kernelObservationSieve_round_trip y)))

instance kernelObservationSieveBHistCarrier :
    BHistCarrier KernelObservationSieveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelObservationSieveToEventFlow
  fromEventFlow := kernelObservationSieveFromEventFlow

instance kernelObservationSieveChapterTasteGate :
    ChapterTasteGate KernelObservationSieveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kernelObservationSieveFromEventFlow
        (kernelObservationSieveToEventFlow x) = some x
    exact kernelObservationSieve_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelObservationSieveToEventFlow_injective heq)

instance kernelObservationSieveFieldFaithful :
    FieldFaithful KernelObservationSieveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | KernelObservationSieveUp.mk observer selector filter accepted rejected transport routes
        provenance nameCert =>
        [observer, selector, filter, accepted, rejected, transport, routes, provenance,
          nameCert]
  field_faithful := by
    intro x y h
    cases x with
    | mk observer₁ selector₁ filter₁ accepted₁ rejected₁ transport₁ routes₁ provenance₁
        nameCert₁ =>
        cases y with
        | mk observer₂ selector₂ filter₂ accepted₂ rejected₂ transport₂ routes₂ provenance₂
            nameCert₂ =>
            simp only [] at h
            cases h
            rfl

instance kernelObservationSieveNontrivial :
    Nontrivial KernelObservationSieveUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KernelObservationSieveUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KernelObservationSieveUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate KernelObservationSieveUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kernelObservationSieveChapterTasteGate

theorem KernelObservationSieveTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kernelObservationSieveDecodeBHist
        (kernelObservationSieveEncodeBHist h) = h) ∧
      (∀ x : KernelObservationSieveUp,
        kernelObservationSieveFromEventFlow
          (kernelObservationSieveToEventFlow x) = some x) ∧
        (∀ x y : KernelObservationSieveUp,
          kernelObservationSieveToEventFlow x =
            kernelObservationSieveToEventFlow y → x = y) ∧
          kernelObservationSieveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelObservationSieveDecode_encode_bhist
  · constructor
    · exact kernelObservationSieve_round_trip
    · constructor
      · intro x y heq
        exact kernelObservationSieveToEventFlow_injective heq
      · rfl

end BEDC.Derived.KernelObservationSieveUp.TasteGate
