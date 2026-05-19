import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RelationalObjectivityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RelationalObjectivityUp : Type where
  | mk (F I A L T P N : BHist) : RelationalObjectivityUp
  deriving DecidableEq

def relationalObjectivityEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: relationalObjectivityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: relationalObjectivityEncodeBHist h

def relationalObjectivityDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (relationalObjectivityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (relationalObjectivityDecodeBHist tail)

private theorem RelationalObjectivityTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      relationalObjectivityDecodeBHist (relationalObjectivityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def relationalObjectivityToEventFlow : RelationalObjectivityUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RelationalObjectivityUp.mk F I A L T P N =>
      [[BMark.b0],
        relationalObjectivityEncodeBHist F,
        [BMark.b1, BMark.b0],
        relationalObjectivityEncodeBHist I,
        [BMark.b1, BMark.b1, BMark.b0],
        relationalObjectivityEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalObjectivityEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalObjectivityEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalObjectivityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        relationalObjectivityEncodeBHist N]

private def relationalObjectivityDecodePacket
    (F I A L T P N : RawEvent) : RelationalObjectivityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RelationalObjectivityUp.mk
    (relationalObjectivityDecodeBHist F)
    (relationalObjectivityDecodeBHist I)
    (relationalObjectivityDecodeBHist A)
    (relationalObjectivityDecodeBHist L)
    (relationalObjectivityDecodeBHist T)
    (relationalObjectivityDecodeBHist P)
    (relationalObjectivityDecodeBHist N)

def relationalObjectivityFromEventFlow : EventFlow -> Option RelationalObjectivityUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | F :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | I :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | A :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | L :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | T :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | P :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | N :: rest13 =>
                                                          match rest13 with
                                                          | [] =>
                                                              some
                                                                (relationalObjectivityDecodePacket
                                                                  F I A L T P N)
                                                          | _ :: _ => none

private theorem RelationalObjectivityTasteGate_single_carrier_alignment_round_trip :
    forall x : RelationalObjectivityUp,
      relationalObjectivityFromEventFlow (relationalObjectivityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F I A L T P N =>
      change
        some
          (relationalObjectivityDecodePacket
            (relationalObjectivityEncodeBHist F)
            (relationalObjectivityEncodeBHist I)
            (relationalObjectivityEncodeBHist A)
            (relationalObjectivityEncodeBHist L)
            (relationalObjectivityEncodeBHist T)
            (relationalObjectivityEncodeBHist P)
            (relationalObjectivityEncodeBHist N)) =
          some (RelationalObjectivityUp.mk F I A L T P N)
      unfold relationalObjectivityDecodePacket
      rw [RelationalObjectivityTasteGate_single_carrier_alignment_decode F,
        RelationalObjectivityTasteGate_single_carrier_alignment_decode I,
        RelationalObjectivityTasteGate_single_carrier_alignment_decode A,
        RelationalObjectivityTasteGate_single_carrier_alignment_decode L,
        RelationalObjectivityTasteGate_single_carrier_alignment_decode T,
        RelationalObjectivityTasteGate_single_carrier_alignment_decode P,
        RelationalObjectivityTasteGate_single_carrier_alignment_decode N]

private theorem RelationalObjectivityTasteGate_single_carrier_alignment_injective
    {x y : RelationalObjectivityUp} :
    relationalObjectivityToEventFlow x = relationalObjectivityToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      relationalObjectivityFromEventFlow (relationalObjectivityToEventFlow x) =
        relationalObjectivityFromEventFlow (relationalObjectivityToEventFlow y) :=
    congrArg relationalObjectivityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RelationalObjectivityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RelationalObjectivityTasteGate_single_carrier_alignment_round_trip y)))

private def relationalObjectivityFields : RelationalObjectivityUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RelationalObjectivityUp.mk F I A L T P N => [F, I, A, L, T, P, N]

private theorem RelationalObjectivityTasteGate_single_carrier_alignment_fields :
    forall x y : RelationalObjectivityUp,
      relationalObjectivityFields x = relationalObjectivityFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 I1 A1 L1 T1 P1 N1 =>
      cases y with
      | mk F2 I2 A2 L2 T2 P2 N2 =>
          cases hfields
          rfl

instance relationalObjectivityBHistCarrier : BHistCarrier RelationalObjectivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := relationalObjectivityToEventFlow
  fromEventFlow := relationalObjectivityFromEventFlow

instance relationalObjectivityChapterTasteGate :
    ChapterTasteGate RelationalObjectivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change relationalObjectivityFromEventFlow (relationalObjectivityToEventFlow x) = some x
    exact RelationalObjectivityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RelationalObjectivityTasteGate_single_carrier_alignment_injective heq)

instance relationalObjectivityFieldFaithful :
    FieldFaithful RelationalObjectivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := relationalObjectivityFields
  field_faithful := RelationalObjectivityTasteGate_single_carrier_alignment_fields

instance relationalObjectivityNontrivial : Nontrivial RelationalObjectivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RelationalObjectivityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RelationalObjectivityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RelationalObjectivityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  relationalObjectivityChapterTasteGate

def RelationalObjectivityCarrier (F I A L T P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  UnaryHistory F ∧ UnaryHistory I ∧ UnaryHistory A ∧ UnaryHistory L ∧
    UnaryHistory T ∧ UnaryHistory P ∧ UnaryHistory N ∧ Cont I A T ∧
      Cont L T N ∧ hsame P P

def RelationalObjectivityNameCertClassifier
    (F I A L T P N F' I' A' L' T' P' N' : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist hsame RelationalObjectivityCarrier
  RelationalObjectivityCarrier F I A L T P N ∧
    RelationalObjectivityCarrier F' I' A' L' T' P' N' ∧
      hsame F F' ∧ hsame I I' ∧ hsame A A' ∧ hsame L L' ∧
        hsame T T' ∧ hsame P P' ∧ hsame N N'

theorem RelationalObjectivityNameCertClassifier_transport
    {F I A L T P N F' I' A' L' T' P' N' : BHist} :
    RelationalObjectivityNameCertClassifier F I A L T P N F' I' A' L' T' P' N' ->
      hsame N N' := by
  -- BEDC touchpoint anchor: BHist hsame RelationalObjectivityCarrier
  intro classifier
  exact classifier.right.right.right.right.right.right.right.right

theorem RelationalObjectivityTasteGate_single_carrier_alignment :
    (∀ h : BHist, relationalObjectivityDecodeBHist (relationalObjectivityEncodeBHist h) = h) ∧
      (∀ x : RelationalObjectivityUp,
        relationalObjectivityFromEventFlow (relationalObjectivityToEventFlow x) = some x) ∧
        (∀ x y : RelationalObjectivityUp,
          relationalObjectivityToEventFlow x = relationalObjectivityToEventFlow y → x = y) ∧
          relationalObjectivityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨RelationalObjectivityTasteGate_single_carrier_alignment_decode,
      RelationalObjectivityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => RelationalObjectivityTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

theorem RelationalObjectivityInvariantLedgerExactness
    {F I A L T P N replay evidence : BHist} :
    relationalObjectivityFields (RelationalObjectivityUp.mk F I A L T P N) =
      [F, I, A, L, T, P, N] →
      Cont L T replay →
        hsame replay evidence →
          UnaryHistory L →
            UnaryHistory T →
              UnaryHistory replay ∧ Cont L T replay ∧ hsame replay evidence := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro hfields ledgerReplay replayEvidence ledgerUnary transportUnary
  cases hfields
  have replayUnary : UnaryHistory replay :=
    unary_cont_closed ledgerUnary transportUnary ledgerReplay
  exact ⟨replayUnary, ledgerReplay, replayEvidence⟩

theorem RelationalObjectivityNoPrivilegedAnchorCertificate
    {F I A L T P N anchorReplay invariantReplay : BHist} :
    relationalObjectivityFields (RelationalObjectivityUp.mk F I A L T P N) =
      [F, I, A, L, T, P, N] →
      Cont A T anchorReplay →
        Cont I A invariantReplay →
          UnaryHistory I →
            UnaryHistory A →
              UnaryHistory T →
                UnaryHistory anchorReplay ∧
                  UnaryHistory invariantReplay ∧
                    Cont A T anchorReplay ∧
                      Cont I A invariantReplay ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame
  intro hfields anchorRoute invariantRoute invariantUnary anchorUnary transportUnary
  cases hfields
  have anchorReplayUnary : UnaryHistory anchorReplay :=
    unary_cont_closed anchorUnary transportUnary anchorRoute
  have invariantReplayUnary : UnaryHistory invariantReplay :=
    unary_cont_closed invariantUnary anchorUnary invariantRoute
  exact
    ⟨anchorReplayUnary, invariantReplayUnary, anchorRoute, invariantRoute, hsame_refl N⟩

theorem RelationalObjectivityCarrier_no_privileged_anchor_certificate
    {F I A L T P N anchor replay : BHist} :
    relationalObjectivityFields (RelationalObjectivityUp.mk F I A L T P N) =
      [F, I, A, L, T, P, N] →
      Cont A T anchor →
        hsame anchor replay →
          UnaryHistory A →
            UnaryHistory T →
              UnaryHistory anchor ∧ Cont A T anchor ∧ hsame anchor replay := by
  -- BEDC touchpoint anchor: BHist BMark Cont hsame UnaryHistory
  intro hfields anchorRoute anchorReplay anchorUnary transportUnary
  cases hfields
  have anchorHistory : UnaryHistory anchor :=
    unary_cont_closed anchorUnary transportUnary anchorRoute
  exact ⟨anchorHistory, anchorRoute, anchorReplay⟩

theorem RelationalObjectivityAnchorStabilityObligation
    {F I A L T P N anchorReplay invariantReplay : BHist} :
    RelationalObjectivityCarrier F I A L T P N ->
      Cont A T anchorReplay ->
        Cont I A invariantReplay ->
          UnaryHistory anchorReplay ∧ UnaryHistory invariantReplay ∧
            Cont A T anchorReplay ∧ Cont I A invariantReplay ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier anchorRoute invariantRoute
  obtain ⟨_familyUnary, invariantUnary, anchorUnary, _ledgerUnary, transportUnary,
    _provenanceUnary, _nameUnary, _invariantAnchorTransport, _ledgerTransportName,
    _provenanceSelf⟩ := carrier
  have anchorReplayUnary : UnaryHistory anchorReplay :=
    unary_cont_closed anchorUnary transportUnary anchorRoute
  have invariantReplayUnary : UnaryHistory invariantReplay :=
    unary_cont_closed invariantUnary anchorUnary invariantRoute
  exact
    ⟨anchorReplayUnary, invariantReplayUnary, anchorRoute, invariantRoute,
      hsame_refl N⟩

theorem RelationalObjectivityNameCertClassifier_semantic_certificate
    {F I A L T P N : BHist} :
    RelationalObjectivityCarrier F I A L T P N ->
      SemanticNameCert
        (fun row : BHist =>
          RelationalObjectivityCarrier F I A L T P N ∧
            (hsame row F ∨ hsame row I ∨ hsame row A ∨ hsame row L ∨
              hsame row T ∨ hsame row P ∨ hsame row N))
        (fun row : BHist =>
          RelationalObjectivityCarrier F I A L T P N ∧
            (hsame row F ∨ hsame row I ∨ hsame row A ∨ hsame row L ∨
              hsame row T ∨ hsame row P ∨ hsame row N))
        (fun row : BHist =>
          UnaryHistory row ∧
            (hsame row F ∨ hsame row I ∨ hsame row A ∨ hsame row L ∨
              hsame row T ∨ hsame row P ∨ hsame row N))
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame UnaryHistory SemanticNameCert RelationalObjectivityCarrier
  intro carrier
  have carrierWitness : RelationalObjectivityCarrier F I A L T P N := carrier
  obtain ⟨familyUnary, invariantUnary, anchorUnary, ledgerUnary, transportUnary,
    provenanceUnary, nameUnary, _invariantAnchorTransport, _ledgerTransportName,
    _provenanceSelf⟩ := carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro F ⟨carrierWitness, Or.inl (hsame_refl F)⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact source.left
        · cases source.right with
          | inl sameF =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameF)
          | inr rest =>
              cases rest with
              | inl sameI =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameI))
              | inr rest =>
                  cases rest with
                  | inl sameA =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameA)))
                  | inr rest =>
                      cases rest with
                      | inl sameL =>
                          exact Or.inr
                            (Or.inr
                              (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameL))))
                      | inr rest =>
                          cases rest with
                          | inl sameT =>
                              exact Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inl
                                        (hsame_trans (hsame_symm sameRows) sameT)))))
                          | inr rest =>
                              cases rest with
                              | inl sameP =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameP))))))
                              | inr sameN =>
                                  exact Or.inr
                                    (Or.inr
                                      (Or.inr
                                        (Or.inr
                                          (Or.inr
                                            (Or.inr
                                              (hsame_trans (hsame_symm sameRows)
                                                sameN))))))
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro row source
      cases source.right with
      | inl sameF =>
          exact ⟨unary_transport_symm familyUnary sameF, Or.inl sameF⟩
      | inr rest =>
          cases rest with
          | inl sameI =>
              exact ⟨unary_transport_symm invariantUnary sameI, Or.inr (Or.inl sameI)⟩
          | inr rest =>
              cases rest with
              | inl sameA =>
                  exact
                    ⟨unary_transport_symm anchorUnary sameA,
                      Or.inr (Or.inr (Or.inl sameA))⟩
              | inr rest =>
                  cases rest with
                  | inl sameL =>
                      exact
                        ⟨unary_transport_symm ledgerUnary sameL,
                          Or.inr (Or.inr (Or.inr (Or.inl sameL)))⟩
                  | inr rest =>
                      cases rest with
                      | inl sameT =>
                          exact
                            ⟨unary_transport_symm transportUnary sameT,
                              Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameT))))⟩
                      | inr rest =>
                          cases rest with
                          | inl sameP =>
                              exact
                                ⟨unary_transport_symm provenanceUnary sameP,
                                  Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inr (Or.inr (Or.inl sameP)))))⟩
                          | inr sameN =>
                              exact
                                ⟨unary_transport_symm nameUnary sameN,
                                  Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inr (Or.inr (Or.inr sameN)))))⟩
  }

end BEDC.Derived.RelationalObjectivityUp
