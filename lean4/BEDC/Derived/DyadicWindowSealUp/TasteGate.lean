import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicWindowSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicWindowSealUp : Type where
  | mk :
      (request window readback budget synchronizer sealRow transport route provenance
        name : BHist) →
      DyadicWindowSealUp
  deriving DecidableEq

def dyadicWindowSealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicWindowSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicWindowSealEncodeBHist h

def dyadicWindowSealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicWindowSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicWindowSealDecodeBHist tail)

private theorem dyadicWindowSealDecodeEncodeBHist :
    ∀ h : BHist, dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicWindowSealFields : DyadicWindowSealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicWindowSealUp.mk request window readback budget synchronizer sealRow transport route
      provenance name =>
      [request, window, readback, budget, synchronizer, sealRow, transport, route, provenance,
        name]

def dyadicWindowSealToEventFlow : DyadicWindowSealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicWindowSealFields x).map dyadicWindowSealEncodeBHist

def dyadicWindowSealFromEventFlow : EventFlow → Option DyadicWindowSealUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | request :: rest0 =>
      match rest0 with
      | [] => none
      | window :: rest1 =>
          match rest1 with
          | [] => none
          | readback :: rest2 =>
              match rest2 with
              | [] => none
              | budget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | synchronizer :: rest4 =>
                      match rest4 with
                      | [] => none
                      | sealRow :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | route :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | name :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (DyadicWindowSealUp.mk
                                                  (dyadicWindowSealDecodeBHist request)
                                                  (dyadicWindowSealDecodeBHist window)
                                                  (dyadicWindowSealDecodeBHist readback)
                                                  (dyadicWindowSealDecodeBHist budget)
                                                  (dyadicWindowSealDecodeBHist synchronizer)
                                                  (dyadicWindowSealDecodeBHist sealRow)
                                                  (dyadicWindowSealDecodeBHist transport)
                                                  (dyadicWindowSealDecodeBHist route)
                                                  (dyadicWindowSealDecodeBHist provenance)
                                                  (dyadicWindowSealDecodeBHist name))
                                          | _ :: _ => none

private theorem dyadicWindowSeal_round_trip :
    ∀ x : DyadicWindowSealUp,
      dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk request window readback budget synchronizer sealRow transport route provenance name =>
      change
        some
          (DyadicWindowSealUp.mk
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist request))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist window))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist readback))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist budget))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist synchronizer))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist sealRow))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist transport))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist route))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist provenance))
            (dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist name))) =
          some
            (DyadicWindowSealUp.mk request window readback budget synchronizer sealRow
              transport route provenance name)
      rw [dyadicWindowSealDecodeEncodeBHist request, dyadicWindowSealDecodeEncodeBHist window,
        dyadicWindowSealDecodeEncodeBHist readback, dyadicWindowSealDecodeEncodeBHist budget,
        dyadicWindowSealDecodeEncodeBHist synchronizer,
        dyadicWindowSealDecodeEncodeBHist sealRow,
        dyadicWindowSealDecodeEncodeBHist transport, dyadicWindowSealDecodeEncodeBHist route,
        dyadicWindowSealDecodeEncodeBHist provenance, dyadicWindowSealDecodeEncodeBHist name]

private theorem dyadicWindowSealToEventFlow_injective {x y : DyadicWindowSealUp} :
    dyadicWindowSealToEventFlow x = dyadicWindowSealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow x) =
        dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow y) :=
    congrArg dyadicWindowSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicWindowSeal_round_trip x).symm
      (Eq.trans hread (dyadicWindowSeal_round_trip y)))

private theorem dyadicWindowSeal_fields_faithful :
    ∀ x y : DyadicWindowSealUp, dyadicWindowSealFields x = dyadicWindowSealFields y → x = y :=
    by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk request₁ window₁ readback₁ budget₁ synchronizer₁ sealRow₁ transport₁ route₁
      provenance₁ name₁ =>
      cases y with
      | mk request₂ window₂ readback₂ budget₂ synchronizer₂ sealRow₂ transport₂ route₂
          provenance₂ name₂ =>
          injection hfields with hRequest tail0
          injection tail0 with hWindow tail1
          injection tail1 with hReadback tail2
          injection tail2 with hBudget tail3
          injection tail3 with hSynchronizer tail4
          injection tail4 with hSealRow tail5
          injection tail5 with hTransport tail6
          injection tail6 with hRoute tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hName _
          subst hRequest
          subst hWindow
          subst hReadback
          subst hBudget
          subst hSynchronizer
          subst hSealRow
          subst hTransport
          subst hRoute
          subst hProvenance
          subst hName
          rfl

instance dyadicWindowSealBHistCarrier : BHistCarrier DyadicWindowSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicWindowSealToEventFlow
  fromEventFlow := dyadicWindowSealFromEventFlow

instance dyadicWindowSealChapterTasteGate : ChapterTasteGate DyadicWindowSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow x) = some x
    exact dyadicWindowSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicWindowSealToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicWindowSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow x) = some x
    exact dyadicWindowSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicWindowSealToEventFlow_injective heq)

instance dyadicWindowSealFieldFaithful : FieldFaithful DyadicWindowSealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicWindowSealFields
  field_faithful := dyadicWindowSeal_fields_faithful

instance dyadicWindowSealNontrivial : Nontrivial DyadicWindowSealUp where
  witness_pair :=
    ⟨DyadicWindowSealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicWindowSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

theorem DyadicWindowSealTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicWindowSealDecodeBHist (dyadicWindowSealEncodeBHist h) = h) ∧
      (∀ x : DyadicWindowSealUp,
        dyadicWindowSealFromEventFlow (dyadicWindowSealToEventFlow x) = some x) ∧
        (∀ x y : DyadicWindowSealUp,
          dyadicWindowSealToEventFlow x = dyadicWindowSealToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful DyadicWindowSealUp) ∧
            Nonempty (Nontrivial DyadicWindowSealUp) ∧
              dyadicWindowSealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact dyadicWindowSealDecodeEncodeBHist
  · constructor
    · exact dyadicWindowSeal_round_trip
    · constructor
      · intro x y heq
        exact dyadicWindowSealToEventFlow_injective heq
      · constructor
        · exact ⟨dyadicWindowSealFieldFaithful⟩
        · constructor
          · exact ⟨dyadicWindowSealNontrivial⟩
          · rfl

end BEDC.Derived.DyadicWindowSealUp
