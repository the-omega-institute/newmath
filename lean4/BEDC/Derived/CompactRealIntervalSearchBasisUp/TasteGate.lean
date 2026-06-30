import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactRealIntervalSearchBasisUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactRealIntervalSearchBasisUp : Type where
  | mk :
      (compact located finiteSearch dyadic window readback realSeal transport replay
        provenance localName : BHist) →
        CompactRealIntervalSearchBasisUp
  deriving DecidableEq

def compactRealIntervalSearchBasisEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactRealIntervalSearchBasisEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactRealIntervalSearchBasisEncodeBHist h

def compactRealIntervalSearchBasisDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactRealIntervalSearchBasisDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactRealIntervalSearchBasisDecodeBHist tail)

private theorem CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      compactRealIntervalSearchBasisDecodeBHist
          (compactRealIntervalSearchBasisEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactRealIntervalSearchBasisFields :
    CompactRealIntervalSearchBasisUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactRealIntervalSearchBasisUp.mk compact located finiteSearch dyadic window readback
      realSeal transport replay provenance localName =>
      [compact, located, finiteSearch, dyadic, window, readback, realSeal, transport,
        replay, provenance, localName]

def compactRealIntervalSearchBasisToEventFlow :
    CompactRealIntervalSearchBasisUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (compactRealIntervalSearchBasisFields x).map
        compactRealIntervalSearchBasisEncodeBHist

def compactRealIntervalSearchBasisFromEventFlow
    (flow : EventFlow) : Option CompactRealIntervalSearchBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | compact :: rest1 =>
      match rest1 with
      | [] => none
      | located :: rest2 =>
          match rest2 with
          | [] => none
          | finiteSearch :: rest3 =>
              match rest3 with
              | [] => none
              | dyadic :: rest4 =>
                  match rest4 with
                  | [] => none
                  | window :: rest5 =>
                      match rest5 with
                      | [] => none
                      | readback :: rest6 =>
                          match rest6 with
                          | [] => none
                          | realSeal :: rest7 =>
                              match rest7 with
                              | [] => none
                              | transport :: rest8 =>
                                  match rest8 with
                                  | [] => none
                                  | replay :: rest9 =>
                                      match rest9 with
                                      | [] => none
                                      | provenance :: rest10 =>
                                          match rest10 with
                                          | [] => none
                                          | localName :: rest11 =>
                                              match rest11 with
                                              | [] =>
                                                  some
                                                    (CompactRealIntervalSearchBasisUp.mk
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        compact)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        located)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        finiteSearch)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        dyadic)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        window)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        readback)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        realSeal)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        transport)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        replay)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        provenance)
                                                      (compactRealIntervalSearchBasisDecodeBHist
                                                        localName))
                                              | _ :: _ => none

private theorem CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_round_trip
    (x : CompactRealIntervalSearchBasisUp) :
    compactRealIntervalSearchBasisFromEventFlow
        (compactRealIntervalSearchBasisToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk compact located finiteSearch dyadic window readback realSeal transport replay
      provenance localName =>
      change
        some
          (CompactRealIntervalSearchBasisUp.mk
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist compact))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist located))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist finiteSearch))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist dyadic))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist window))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist readback))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist realSeal))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist transport))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist replay))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist provenance))
            (compactRealIntervalSearchBasisDecodeBHist
              (compactRealIntervalSearchBasisEncodeBHist localName))) =
          some
            (CompactRealIntervalSearchBasisUp.mk compact located finiteSearch dyadic window
              readback realSeal transport replay provenance localName)
      exact
        Eq.trans
          (congrArg
            (fun z =>
              some
                (CompactRealIntervalSearchBasisUp.mk z
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist located))
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist finiteSearch))
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist dyadic))
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist window))
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist readback))
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist realSeal))
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist transport))
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist replay))
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist provenance))
                  (compactRealIntervalSearchBasisDecodeBHist
                    (compactRealIntervalSearchBasisEncodeBHist localName))))
            (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
              compact))
          (Eq.trans
            (congrArg
              (fun z =>
                some
                  (CompactRealIntervalSearchBasisUp.mk compact z
                    (compactRealIntervalSearchBasisDecodeBHist
                      (compactRealIntervalSearchBasisEncodeBHist finiteSearch))
                    (compactRealIntervalSearchBasisDecodeBHist
                      (compactRealIntervalSearchBasisEncodeBHist dyadic))
                    (compactRealIntervalSearchBasisDecodeBHist
                      (compactRealIntervalSearchBasisEncodeBHist window))
                    (compactRealIntervalSearchBasisDecodeBHist
                      (compactRealIntervalSearchBasisEncodeBHist readback))
                    (compactRealIntervalSearchBasisDecodeBHist
                      (compactRealIntervalSearchBasisEncodeBHist realSeal))
                    (compactRealIntervalSearchBasisDecodeBHist
                      (compactRealIntervalSearchBasisEncodeBHist transport))
                    (compactRealIntervalSearchBasisDecodeBHist
                      (compactRealIntervalSearchBasisEncodeBHist replay))
                    (compactRealIntervalSearchBasisDecodeBHist
                      (compactRealIntervalSearchBasisEncodeBHist provenance))
                    (compactRealIntervalSearchBasisDecodeBHist
                      (compactRealIntervalSearchBasisEncodeBHist localName))))
              (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                located))
            (Eq.trans
              (congrArg
                (fun z =>
                  some
                    (CompactRealIntervalSearchBasisUp.mk compact located z
                      (compactRealIntervalSearchBasisDecodeBHist
                        (compactRealIntervalSearchBasisEncodeBHist dyadic))
                      (compactRealIntervalSearchBasisDecodeBHist
                        (compactRealIntervalSearchBasisEncodeBHist window))
                      (compactRealIntervalSearchBasisDecodeBHist
                        (compactRealIntervalSearchBasisEncodeBHist readback))
                      (compactRealIntervalSearchBasisDecodeBHist
                        (compactRealIntervalSearchBasisEncodeBHist realSeal))
                      (compactRealIntervalSearchBasisDecodeBHist
                        (compactRealIntervalSearchBasisEncodeBHist transport))
                      (compactRealIntervalSearchBasisDecodeBHist
                        (compactRealIntervalSearchBasisEncodeBHist replay))
                      (compactRealIntervalSearchBasisDecodeBHist
                        (compactRealIntervalSearchBasisEncodeBHist provenance))
                      (compactRealIntervalSearchBasisDecodeBHist
                        (compactRealIntervalSearchBasisEncodeBHist localName))))
                (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                  finiteSearch))
              (Eq.trans
                (congrArg
                  (fun z =>
                    some
                      (CompactRealIntervalSearchBasisUp.mk compact located finiteSearch z
                        (compactRealIntervalSearchBasisDecodeBHist
                          (compactRealIntervalSearchBasisEncodeBHist window))
                        (compactRealIntervalSearchBasisDecodeBHist
                          (compactRealIntervalSearchBasisEncodeBHist readback))
                        (compactRealIntervalSearchBasisDecodeBHist
                          (compactRealIntervalSearchBasisEncodeBHist realSeal))
                        (compactRealIntervalSearchBasisDecodeBHist
                          (compactRealIntervalSearchBasisEncodeBHist transport))
                        (compactRealIntervalSearchBasisDecodeBHist
                          (compactRealIntervalSearchBasisEncodeBHist replay))
                        (compactRealIntervalSearchBasisDecodeBHist
                          (compactRealIntervalSearchBasisEncodeBHist provenance))
                        (compactRealIntervalSearchBasisDecodeBHist
                          (compactRealIntervalSearchBasisEncodeBHist localName))))
                  (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                    dyadic))
                (Eq.trans
                  (congrArg
                    (fun z =>
                      some
                        (CompactRealIntervalSearchBasisUp.mk compact located finiteSearch
                          dyadic z
                          (compactRealIntervalSearchBasisDecodeBHist
                            (compactRealIntervalSearchBasisEncodeBHist readback))
                          (compactRealIntervalSearchBasisDecodeBHist
                            (compactRealIntervalSearchBasisEncodeBHist realSeal))
                          (compactRealIntervalSearchBasisDecodeBHist
                            (compactRealIntervalSearchBasisEncodeBHist transport))
                          (compactRealIntervalSearchBasisDecodeBHist
                            (compactRealIntervalSearchBasisEncodeBHist replay))
                          (compactRealIntervalSearchBasisDecodeBHist
                            (compactRealIntervalSearchBasisEncodeBHist provenance))
                          (compactRealIntervalSearchBasisDecodeBHist
                            (compactRealIntervalSearchBasisEncodeBHist localName))))
                    (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                      window))
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        some
                          (CompactRealIntervalSearchBasisUp.mk compact located finiteSearch
                            dyadic window z
                            (compactRealIntervalSearchBasisDecodeBHist
                              (compactRealIntervalSearchBasisEncodeBHist realSeal))
                            (compactRealIntervalSearchBasisDecodeBHist
                              (compactRealIntervalSearchBasisEncodeBHist transport))
                            (compactRealIntervalSearchBasisDecodeBHist
                              (compactRealIntervalSearchBasisEncodeBHist replay))
                            (compactRealIntervalSearchBasisDecodeBHist
                              (compactRealIntervalSearchBasisEncodeBHist provenance))
                            (compactRealIntervalSearchBasisDecodeBHist
                              (compactRealIntervalSearchBasisEncodeBHist localName))))
                      (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                        readback))
                    (Eq.trans
                      (congrArg
                        (fun z =>
                          some
                            (CompactRealIntervalSearchBasisUp.mk compact located finiteSearch
                              dyadic window readback z
                              (compactRealIntervalSearchBasisDecodeBHist
                                (compactRealIntervalSearchBasisEncodeBHist transport))
                              (compactRealIntervalSearchBasisDecodeBHist
                                (compactRealIntervalSearchBasisEncodeBHist replay))
                              (compactRealIntervalSearchBasisDecodeBHist
                                (compactRealIntervalSearchBasisEncodeBHist provenance))
                              (compactRealIntervalSearchBasisDecodeBHist
                                (compactRealIntervalSearchBasisEncodeBHist localName))))
                        (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                          realSeal))
                      (Eq.trans
                        (congrArg
                          (fun z =>
                            some
                              (CompactRealIntervalSearchBasisUp.mk compact located
                                finiteSearch dyadic window readback realSeal z
                                (compactRealIntervalSearchBasisDecodeBHist
                                  (compactRealIntervalSearchBasisEncodeBHist replay))
                                (compactRealIntervalSearchBasisDecodeBHist
                                  (compactRealIntervalSearchBasisEncodeBHist provenance))
                                (compactRealIntervalSearchBasisDecodeBHist
                                  (compactRealIntervalSearchBasisEncodeBHist localName))))
                          (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                            transport))
                        (Eq.trans
                          (congrArg
                            (fun z =>
                              some
                                (CompactRealIntervalSearchBasisUp.mk compact located
                                  finiteSearch dyadic window readback realSeal transport z
                                  (compactRealIntervalSearchBasisDecodeBHist
                                    (compactRealIntervalSearchBasisEncodeBHist provenance))
                                  (compactRealIntervalSearchBasisDecodeBHist
                                    (compactRealIntervalSearchBasisEncodeBHist localName))))
                            (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                              replay))
                          (Eq.trans
                            (congrArg
                              (fun z =>
                                some
                                  (CompactRealIntervalSearchBasisUp.mk compact located
                                    finiteSearch dyadic window readback realSeal transport replay
                                    z
                                    (compactRealIntervalSearchBasisDecodeBHist
                                      (compactRealIntervalSearchBasisEncodeBHist localName))))
                              (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                                provenance))
                            (congrArg
                              (fun z =>
                                some
                                  (CompactRealIntervalSearchBasisUp.mk compact located
                                    finiteSearch dyadic window readback realSeal transport replay
                                    provenance z))
                              (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_decode_encode
                                localName)))))))))))

private theorem CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CompactRealIntervalSearchBasisUp} :
    compactRealIntervalSearchBasisToEventFlow x =
        compactRealIntervalSearchBasisToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactRealIntervalSearchBasisFromEventFlow
          (compactRealIntervalSearchBasisToEventFlow x) =
        compactRealIntervalSearchBasisFromEventFlow
          (compactRealIntervalSearchBasisToEventFlow y) :=
    congrArg compactRealIntervalSearchBasisFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_fields_faithful
    (x y : CompactRealIntervalSearchBasisUp) :
    compactRealIntervalSearchBasisFields x = compactRealIntervalSearchBasisFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  cases x with
  | mk compact₁ located₁ finiteSearch₁ dyadic₁ window₁ readback₁ realSeal₁ transport₁
      replay₁ provenance₁ localName₁ =>
      cases y with
      | mk compact₂ located₂ finiteSearch₂ dyadic₂ window₂ readback₂ realSeal₂ transport₂
          replay₂ provenance₂ localName₂ =>
          injection h with hCompact tail0
          injection tail0 with hLocated tail1
          injection tail1 with hFiniteSearch tail2
          injection tail2 with hDyadic tail3
          injection tail3 with hWindow tail4
          injection tail4 with hReadback tail5
          injection tail5 with hRealSeal tail6
          injection tail6 with hTransport tail7
          injection tail7 with hReplay tail8
          injection tail8 with hProvenance tail9
          injection tail9 with hLocalName _
          subst hCompact
          subst hLocated
          subst hFiniteSearch
          subst hDyadic
          subst hWindow
          subst hReadback
          subst hRealSeal
          subst hTransport
          subst hReplay
          subst hProvenance
          subst hLocalName
          rfl

instance compactRealIntervalSearchBasisBHistCarrier :
    BHistCarrier CompactRealIntervalSearchBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactRealIntervalSearchBasisToEventFlow
  fromEventFlow := compactRealIntervalSearchBasisFromEventFlow

instance compactRealIntervalSearchBasisChapterTasteGate :
    ChapterTasteGate CompactRealIntervalSearchBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactRealIntervalSearchBasisFromEventFlow
          (compactRealIntervalSearchBasisToEventFlow x) =
        some x
    exact CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance compactRealIntervalSearchBasisFieldFaithful :
    FieldFaithful CompactRealIntervalSearchBasisUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactRealIntervalSearchBasisFields
  field_faithful := CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_fields_faithful

def taste_gate : ChapterTasteGate CompactRealIntervalSearchBasisUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compactRealIntervalSearchBasisChapterTasteGate

theorem CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment :
    (∀ x : CompactRealIntervalSearchBasisUp,
      compactRealIntervalSearchBasisFromEventFlow
          (compactRealIntervalSearchBasisToEventFlow x) =
        some x) ∧
      (∀ x y : CompactRealIntervalSearchBasisUp,
        compactRealIntervalSearchBasisToEventFlow x =
            compactRealIntervalSearchBasisToEventFlow y →
          x = y) ∧
        compactRealIntervalSearchBasisFields
            (CompactRealIntervalSearchBasisUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty) =
          [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
            BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_round_trip
  · constructor
    · intro x y heq
      exact
        CompactRealIntervalSearchBasisTasteGate_single_carrier_alignment_toEventFlow_injective
          heq
    · rfl

end BEDC.Derived.CompactRealIntervalSearchBasisUp
