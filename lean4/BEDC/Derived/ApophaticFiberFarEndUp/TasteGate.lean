import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ApophaticFiberFarEndUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ApophaticFiberFarEndUp : Type where
  | mk
      (socket fiber ledger boundary inscription transport route provenance name : BHist) :
      ApophaticFiberFarEndUp
  deriving DecidableEq

def apophaticFiberFarEndEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: apophaticFiberFarEndEncodeBHist h
  | BHist.e1 h => BMark.b1 :: apophaticFiberFarEndEncodeBHist h

def apophaticFiberFarEndDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (apophaticFiberFarEndDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (apophaticFiberFarEndDecodeBHist tail)

private theorem apophaticFiberFarEndDecode_encode_bhist :
    ∀ h : BHist,
      apophaticFiberFarEndDecodeBHist
        (apophaticFiberFarEndEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def apophaticFiberFarEndDecodePacket
    (socket fiber ledger boundary inscription transport route provenance name : RawEvent) :
    ApophaticFiberFarEndUp :=
  ApophaticFiberFarEndUp.mk
    (apophaticFiberFarEndDecodeBHist socket)
    (apophaticFiberFarEndDecodeBHist fiber)
    (apophaticFiberFarEndDecodeBHist ledger)
    (apophaticFiberFarEndDecodeBHist boundary)
    (apophaticFiberFarEndDecodeBHist inscription)
    (apophaticFiberFarEndDecodeBHist transport)
    (apophaticFiberFarEndDecodeBHist route)
    (apophaticFiberFarEndDecodeBHist provenance)
    (apophaticFiberFarEndDecodeBHist name)

def apophaticFiberFarEndToEventFlow :
    ApophaticFiberFarEndUp → EventFlow
  | ApophaticFiberFarEndUp.mk socket fiber ledger boundary inscription transport route
      provenance name =>
      [apophaticFiberFarEndEncodeBHist socket,
        apophaticFiberFarEndEncodeBHist fiber,
        apophaticFiberFarEndEncodeBHist ledger,
        apophaticFiberFarEndEncodeBHist boundary,
        apophaticFiberFarEndEncodeBHist inscription,
        apophaticFiberFarEndEncodeBHist transport,
        apophaticFiberFarEndEncodeBHist route,
        apophaticFiberFarEndEncodeBHist provenance,
        apophaticFiberFarEndEncodeBHist name]

def apophaticFiberFarEndFromEventFlow :
    EventFlow → Option ApophaticFiberFarEndUp
  | [] => none
  | socket :: rest0 =>
      match rest0 with
      | [] => none
      | fiber :: rest1 =>
          match rest1 with
          | [] => none
          | ledger :: rest2 =>
              match rest2 with
              | [] => none
              | boundary :: rest3 =>
                  match rest3 with
                  | [] => none
                  | inscription :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (apophaticFiberFarEndDecodePacket socket fiber ledger
                                              boundary inscription transport route provenance name)
                                      | _ :: _ => none

private theorem apophaticFiberFarEnd_round_trip :
    ∀ x : ApophaticFiberFarEndUp,
      apophaticFiberFarEndFromEventFlow
        (apophaticFiberFarEndToEventFlow x) = some x := by
  intro x
  cases x with
  | mk socket fiber ledger boundary inscription transport route provenance name =>
      change
        some
            (apophaticFiberFarEndDecodePacket
              (apophaticFiberFarEndEncodeBHist socket)
              (apophaticFiberFarEndEncodeBHist fiber)
              (apophaticFiberFarEndEncodeBHist ledger)
              (apophaticFiberFarEndEncodeBHist boundary)
              (apophaticFiberFarEndEncodeBHist inscription)
              (apophaticFiberFarEndEncodeBHist transport)
              (apophaticFiberFarEndEncodeBHist route)
              (apophaticFiberFarEndEncodeBHist provenance)
              (apophaticFiberFarEndEncodeBHist name)) =
          some
            (ApophaticFiberFarEndUp.mk socket fiber ledger boundary inscription transport route
              provenance name)
      unfold apophaticFiberFarEndDecodePacket
      rw [apophaticFiberFarEndDecode_encode_bhist socket,
        apophaticFiberFarEndDecode_encode_bhist fiber,
        apophaticFiberFarEndDecode_encode_bhist ledger,
        apophaticFiberFarEndDecode_encode_bhist boundary,
        apophaticFiberFarEndDecode_encode_bhist inscription,
        apophaticFiberFarEndDecode_encode_bhist transport,
        apophaticFiberFarEndDecode_encode_bhist route,
        apophaticFiberFarEndDecode_encode_bhist provenance,
        apophaticFiberFarEndDecode_encode_bhist name]

private theorem apophaticFiberFarEndToEventFlow_injective
    {x y : ApophaticFiberFarEndUp} :
    apophaticFiberFarEndToEventFlow x =
      apophaticFiberFarEndToEventFlow y → x = y := by
  intro heq
  have hread :
      apophaticFiberFarEndFromEventFlow
          (apophaticFiberFarEndToEventFlow x) =
        apophaticFiberFarEndFromEventFlow
          (apophaticFiberFarEndToEventFlow y) :=
    congrArg apophaticFiberFarEndFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (apophaticFiberFarEnd_round_trip x).symm
      (Eq.trans hread (apophaticFiberFarEnd_round_trip y)))

def apophaticFiberFarEndFields :
    ApophaticFiberFarEndUp → List BHist
  | ApophaticFiberFarEndUp.mk socket fiber ledger boundary inscription transport route
      provenance name =>
      [socket, fiber, ledger, boundary, inscription, transport, route, provenance, name]

private theorem apophaticFiberFarEnd_fields_faithful :
    ∀ x y : ApophaticFiberFarEndUp,
      apophaticFiberFarEndFields x =
        apophaticFiberFarEndFields y → x = y := by
  intro x y hfields
  exact apophaticFiberFarEndToEventFlow_injective (by
    cases x with
    | mk socket₁ fiber₁ ledger₁ boundary₁ inscription₁ transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk socket₂ fiber₂ ledger₂ boundary₂ inscription₂ transport₂ route₂ provenance₂ name₂ =>
            injection hfields with hSocket tail0
            injection tail0 with hFiber tail1
            injection tail1 with hLedger tail2
            injection tail2 with hBoundary tail3
            injection tail3 with hInscription tail4
            injection tail4 with hTransport tail5
            injection tail5 with hRoute tail6
            injection tail6 with hProvenance tail7
            injection tail7 with hName _
            subst hSocket
            subst hFiber
            subst hLedger
            subst hBoundary
            subst hInscription
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl)

instance apophaticFiberFarEndBHistCarrier :
    BHistCarrier ApophaticFiberFarEndUp where
  toEventFlow := apophaticFiberFarEndToEventFlow
  fromEventFlow := apophaticFiberFarEndFromEventFlow

instance apophaticFiberFarEndChapterTasteGate :
    ChapterTasteGate ApophaticFiberFarEndUp where
  round_trip := by
    intro x
    change
      apophaticFiberFarEndFromEventFlow
        (apophaticFiberFarEndToEventFlow x) = some x
    exact apophaticFiberFarEnd_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (apophaticFiberFarEndToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ApophaticFiberFarEndUp :=
  apophaticFiberFarEndChapterTasteGate

instance apophaticFiberFarEndFieldFaithful :
    FieldFaithful ApophaticFiberFarEndUp where
  fields := apophaticFiberFarEndFields
  field_faithful := apophaticFiberFarEnd_fields_faithful

instance apophaticFiberFarEndNontrivial :
    Nontrivial ApophaticFiberFarEndUp where
  witness_pair :=
    ⟨ApophaticFiberFarEndUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ApophaticFiberFarEndUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ApophaticFiberFarEndTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      apophaticFiberFarEndDecodeBHist
        (apophaticFiberFarEndEncodeBHist h) = h) ∧
      (∀ x : ApophaticFiberFarEndUp,
        apophaticFiberFarEndFromEventFlow
          (apophaticFiberFarEndToEventFlow x) = some x) ∧
        (∀ x y : ApophaticFiberFarEndUp,
          apophaticFiberFarEndToEventFlow x =
            apophaticFiberFarEndToEventFlow y → x = y) ∧
          Nonempty (FieldFaithful ApophaticFiberFarEndUp) ∧
            Nonempty (Nontrivial ApophaticFiberFarEndUp) ∧
              apophaticFiberFarEndEncodeBHist BHist.Empty = ([] : List BMark) := by
  constructor
  · exact apophaticFiberFarEndDecode_encode_bhist
  · constructor
    · intro x
      change
        apophaticFiberFarEndFromEventFlow
          (apophaticFiberFarEndToEventFlow x) = some x
      exact apophaticFiberFarEnd_round_trip x
    · constructor
      · intro x y heq
        exact apophaticFiberFarEndToEventFlow_injective heq
      · constructor
        · exact ⟨apophaticFiberFarEndFieldFaithful⟩
        · constructor
          · exact ⟨apophaticFiberFarEndNontrivial⟩
          · rfl

end BEDC.Derived.ApophaticFiberFarEndUp
