import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Cont
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NegativeNameBoundaryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NegativeNameBoundaryUp : Type where
  | mk :
      (apophaticHandle socket refusalLedger auditGate transport continuation provenance
        localName : BHist) →
      NegativeNameBoundaryUp
  deriving DecidableEq

def negativeNameBoundaryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: negativeNameBoundaryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: negativeNameBoundaryEncodeBHist h

def negativeNameBoundaryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (negativeNameBoundaryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (negativeNameBoundaryDecodeBHist tail)

private theorem negativeNameBoundaryDecode_encode_bhist :
    ∀ h : BHist, negativeNameBoundaryDecodeBHist (negativeNameBoundaryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem negativeNameBoundary_mk_congr
    {apophaticHandle apophaticHandle' socket socket' refusalLedger refusalLedger'
      auditGate auditGate' transport transport' continuation continuation'
      provenance provenance' localName localName' : BHist}
    (hApophaticHandle : apophaticHandle' = apophaticHandle)
    (hSocket : socket' = socket)
    (hRefusalLedger : refusalLedger' = refusalLedger)
    (hAuditGate : auditGate' = auditGate)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    NegativeNameBoundaryUp.mk apophaticHandle' socket' refusalLedger' auditGate'
        transport' continuation' provenance' localName' =
      NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger auditGate
        transport continuation provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hApophaticHandle
  cases hSocket
  cases hRefusalLedger
  cases hAuditGate
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hLocalName
  rfl

def negativeNameBoundaryToEventFlow : NegativeNameBoundaryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger auditGate transport
      continuation provenance localName =>
      [[BMark.b0],
        negativeNameBoundaryEncodeBHist apophaticHandle,
        [BMark.b1, BMark.b0],
        negativeNameBoundaryEncodeBHist socket,
        [BMark.b1, BMark.b1, BMark.b0],
        negativeNameBoundaryEncodeBHist refusalLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        negativeNameBoundaryEncodeBHist auditGate,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        negativeNameBoundaryEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        negativeNameBoundaryEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        negativeNameBoundaryEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        negativeNameBoundaryEncodeBHist localName]

def negativeNameBoundaryFromEventFlow : EventFlow → Option NegativeNameBoundaryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | apophaticHandle :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | socket :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | refusalLedger :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | auditGate :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | continuation :: rest11 =>
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
                                                              | localName :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (NegativeNameBoundaryUp.mk
                                                                          (negativeNameBoundaryDecodeBHist
                                                                            apophaticHandle)
                                                                          (negativeNameBoundaryDecodeBHist
                                                                            socket)
                                                                          (negativeNameBoundaryDecodeBHist
                                                                            refusalLedger)
                                                                          (negativeNameBoundaryDecodeBHist
                                                                            auditGate)
                                                                          (negativeNameBoundaryDecodeBHist
                                                                            transport)
                                                                          (negativeNameBoundaryDecodeBHist
                                                                            continuation)
                                                                          (negativeNameBoundaryDecodeBHist
                                                                            provenance)
                                                                          (negativeNameBoundaryDecodeBHist
                                                                            localName))
                                                                  | _ :: _ => none

private theorem negativeNameBoundary_round_trip :
    ∀ x : NegativeNameBoundaryUp,
      negativeNameBoundaryFromEventFlow (negativeNameBoundaryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk apophaticHandle socket refusalLedger auditGate transport continuation provenance
      localName =>
      change
        some
          (NegativeNameBoundaryUp.mk
            (negativeNameBoundaryDecodeBHist
              (negativeNameBoundaryEncodeBHist apophaticHandle))
            (negativeNameBoundaryDecodeBHist (negativeNameBoundaryEncodeBHist socket))
            (negativeNameBoundaryDecodeBHist
              (negativeNameBoundaryEncodeBHist refusalLedger))
            (negativeNameBoundaryDecodeBHist (negativeNameBoundaryEncodeBHist auditGate))
            (negativeNameBoundaryDecodeBHist (negativeNameBoundaryEncodeBHist transport))
            (negativeNameBoundaryDecodeBHist
              (negativeNameBoundaryEncodeBHist continuation))
            (negativeNameBoundaryDecodeBHist
              (negativeNameBoundaryEncodeBHist provenance))
            (negativeNameBoundaryDecodeBHist (negativeNameBoundaryEncodeBHist localName))) =
          some
            (NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger auditGate
              transport continuation provenance localName)
      exact
        congrArg some
          (negativeNameBoundary_mk_congr
            (negativeNameBoundaryDecode_encode_bhist apophaticHandle)
            (negativeNameBoundaryDecode_encode_bhist socket)
            (negativeNameBoundaryDecode_encode_bhist refusalLedger)
            (negativeNameBoundaryDecode_encode_bhist auditGate)
            (negativeNameBoundaryDecode_encode_bhist transport)
            (negativeNameBoundaryDecode_encode_bhist continuation)
            (negativeNameBoundaryDecode_encode_bhist provenance)
            (negativeNameBoundaryDecode_encode_bhist localName))

private theorem negativeNameBoundaryToEventFlow_injective
    {x y : NegativeNameBoundaryUp} :
    negativeNameBoundaryToEventFlow x = negativeNameBoundaryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      negativeNameBoundaryFromEventFlow (negativeNameBoundaryToEventFlow x) =
        negativeNameBoundaryFromEventFlow (negativeNameBoundaryToEventFlow y) :=
    congrArg negativeNameBoundaryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (negativeNameBoundary_round_trip x).symm
      (Eq.trans hread (negativeNameBoundary_round_trip y)))

instance negativeNameBoundaryBHistCarrier : BHistCarrier NegativeNameBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := negativeNameBoundaryToEventFlow
  fromEventFlow := negativeNameBoundaryFromEventFlow

instance negativeNameBoundaryChapterTasteGate : ChapterTasteGate NegativeNameBoundaryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change negativeNameBoundaryFromEventFlow (negativeNameBoundaryToEventFlow x) = some x
    exact negativeNameBoundary_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (negativeNameBoundaryToEventFlow_injective heq)

theorem NegativeNameBoundaryTasteGate_single_carrier_alignment :
    (∀ h : BHist, negativeNameBoundaryDecodeBHist (negativeNameBoundaryEncodeBHist h) = h) ∧
      (∀ x : NegativeNameBoundaryUp,
        negativeNameBoundaryFromEventFlow (negativeNameBoundaryToEventFlow x) = some x) ∧
        (∀ x y : NegativeNameBoundaryUp,
          negativeNameBoundaryToEventFlow x = negativeNameBoundaryToEventFlow y → x = y) ∧
          negativeNameBoundaryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact negativeNameBoundaryDecode_encode_bhist
  · constructor
    · exact negativeNameBoundary_round_trip
    · constructor
      · intro x y heq
        exact negativeNameBoundaryToEventFlow_injective heq
      · rfl

theorem NegativeNameBoundary_refusal_ledger
    {apophaticHandle socket refusalLedger auditGate transport continuation provenance
      localName auditRead : BHist}
    (socketRefusalRoute : Cont socket refusalLedger continuation)
    (auditRoute : Cont refusalLedger auditGate auditRead) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row refusalLedger ∧
          ∃ packet : NegativeNameBoundaryUp,
            packet = NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger
              auditGate transport continuation provenance localName)
      (fun row : BHist => hsame row socket ∨ hsame row refusalLedger ∨ hsame row auditGate)
      (fun row : BHist =>
        Cont socket refusalLedger continuation ∧ Cont refusalLedger auditGate auditRead ∧
          hsame row refusalLedger)
      hsame := by
  -- BEDC touchpoint anchor: BHist SemanticNameCert hsame Cont
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro refusalLedger
          ⟨hsame_refl refusalLedger,
            Exists.intro
              (NegativeNameBoundaryUp.mk apophaticHandle socket refusalLedger auditGate
                transport continuation provenance localName)
              rfl⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inl source.left)
    ledger_sound := by
      intro _row source
      exact ⟨socketRefusalRoute, auditRoute, source.left⟩
  }

end BEDC.Derived.NegativeNameBoundaryUp
