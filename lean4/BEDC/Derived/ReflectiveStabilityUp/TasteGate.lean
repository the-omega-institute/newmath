import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ReflectiveStabilityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ReflectiveStabilityUp : Type where
  | mk (S K A Q O F T L H C P N : BHist) : ReflectiveStabilityUp
  deriving DecidableEq

def reflectiveStabilityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: reflectiveStabilityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: reflectiveStabilityEncodeBHist h

def reflectiveStabilityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (reflectiveStabilityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (reflectiveStabilityDecodeBHist tail)

private theorem ReflectiveStabilityTasteGate_single_carrier_alignment_decode :
    forall h : BHist,
      reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def reflectiveStabilityFields : ReflectiveStabilityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ReflectiveStabilityUp.mk S K A Q O F T L H C P N =>
      [S, K, A, Q, O, F, T, L, H, C, P, N]

def reflectiveStabilityToEventFlow : ReflectiveStabilityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ReflectiveStabilityUp.mk S K A Q O F T L H C P N =>
      [[BMark.b0],
        reflectiveStabilityEncodeBHist S,
        [BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        reflectiveStabilityEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        reflectiveStabilityEncodeBHist N]

private def reflectiveStabilityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => reflectiveStabilityEventAtDefault index rest

def reflectiveStabilityFromEventFlow (ef : EventFlow) : Option ReflectiveStabilityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ReflectiveStabilityUp.mk
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 1 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 3 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 5 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 7 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 9 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 11 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 13 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 15 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 17 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 19 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 21 ef))
      (reflectiveStabilityDecodeBHist (reflectiveStabilityEventAtDefault 23 ef)))

private theorem ReflectiveStabilityTasteGate_single_carrier_alignment_round_trip :
    forall x : ReflectiveStabilityUp,
      reflectiveStabilityFromEventFlow (reflectiveStabilityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S K A Q O F T L H C P N =>
      change
        some
          (ReflectiveStabilityUp.mk
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist S))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist K))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist A))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist Q))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist O))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist F))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist T))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist L))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist H))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist C))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist P))
            (reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist N))) =
          some (ReflectiveStabilityUp.mk S K A Q O F T L H C P N)
      rw [ReflectiveStabilityTasteGate_single_carrier_alignment_decode S,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode K,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode A,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode Q,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode O,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode F,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode T,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode L,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode H,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode C,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode P,
        ReflectiveStabilityTasteGate_single_carrier_alignment_decode N]

private theorem ReflectiveStabilityTasteGate_single_carrier_alignment_injective
    {x y : ReflectiveStabilityUp} :
    reflectiveStabilityToEventFlow x = reflectiveStabilityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      reflectiveStabilityFromEventFlow (reflectiveStabilityToEventFlow x) =
        reflectiveStabilityFromEventFlow (reflectiveStabilityToEventFlow y) :=
    congrArg reflectiveStabilityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ReflectiveStabilityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ReflectiveStabilityTasteGate_single_carrier_alignment_round_trip y)))

private theorem ReflectiveStabilityTasteGate_single_carrier_alignment_fields :
    forall x y : ReflectiveStabilityUp,
      reflectiveStabilityFields x = reflectiveStabilityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 K1 A1 Q1 O1 F1 T1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 K2 A2 Q2 O2 F2 T2 L2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance reflectiveStabilityBHistCarrier : BHistCarrier ReflectiveStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := reflectiveStabilityToEventFlow
  fromEventFlow := reflectiveStabilityFromEventFlow

instance reflectiveStabilityChapterTasteGate :
    ChapterTasteGate ReflectiveStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change reflectiveStabilityFromEventFlow (reflectiveStabilityToEventFlow x) = some x
    exact ReflectiveStabilityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (ReflectiveStabilityTasteGate_single_carrier_alignment_injective heq)

instance reflectiveStabilityFieldFaithful : FieldFaithful ReflectiveStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := reflectiveStabilityFields
  field_faithful := ReflectiveStabilityTasteGate_single_carrier_alignment_fields

instance reflectiveStabilityNontrivial : Nontrivial ReflectiveStabilityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ReflectiveStabilityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      ReflectiveStabilityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem ReflectiveStabilityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      reflectiveStabilityDecodeBHist (reflectiveStabilityEncodeBHist h) = h) ∧
      (forall x : ReflectiveStabilityUp,
        reflectiveStabilityFromEventFlow (reflectiveStabilityToEventFlow x) = some x) ∧
        (forall x y : ReflectiveStabilityUp,
          reflectiveStabilityToEventFlow x = reflectiveStabilityToEventFlow y -> x = y) ∧
          reflectiveStabilityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨ReflectiveStabilityTasteGate_single_carrier_alignment_decode,
      ReflectiveStabilityTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => ReflectiveStabilityTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

theorem ReflectiveStabilityCarrier_namecert_obligations
    {S K A Q O F T L H C P N reuseRead ledgerRead : BHist} :
    Cont Q C reuseRead ->
      Cont reuseRead T ledgerRead ->
        UnaryHistory Q ->
          UnaryHistory C ->
            UnaryHistory T ->
              UnaryHistory reuseRead ∧ UnaryHistory ledgerRead ∧
                reflectiveStabilityFields (ReflectiveStabilityUp.mk S K A Q O F T L H C P N) =
                  [S, K, A, Q, O, F, T, L, H, C, P, N] ∧
                SemanticNameCert
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row ledgerRead ∧ Cont Q C reuseRead ∧
                      Cont reuseRead T ledgerRead)
                  (fun row : BHist =>
                    hsame row ledgerRead ∧
                      reflectiveStabilityFields
                          (ReflectiveStabilityUp.mk S K A Q O F T L H C P N) =
                        [S, K, A, Q, O, F, T, L, H, C, P, N])
                  hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont SemanticNameCert hsame
  intro qCReuse reuseTLedger qUnary cUnary tUnary
  have reuseUnary : UnaryHistory reuseRead :=
    unary_cont_closed qUnary cUnary qCReuse
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed reuseUnary tUnary reuseTLedger
  have nameCert :
      SemanticNameCert
        (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row ledgerRead ∧ Cont Q C reuseRead ∧ Cont reuseRead T ledgerRead)
        (fun row : BHist =>
          hsame row ledgerRead ∧
            reflectiveStabilityFields (ReflectiveStabilityUp.mk S K A Q O F T L H C P N) =
              [S, K, A, Q, O, F, T, L, H, C, P, N])
        hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead (And.intro (hsame_refl ledgerRead) ledgerUnary)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          And.intro
            (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact And.intro source.left (And.intro qCReuse reuseTLedger)
    ledger_sound := by
      intro _row source
      exact And.intro source.left rfl
  }
  exact ⟨reuseUnary, ledgerUnary, rfl, nameCert⟩

theorem ReflectiveStabilityCarrier_anchor_stability
    {S K A Q O F T L H C P N sourceAnchor checkpointAnchor auditAnchor
      observationAnchor interfaceAnchor : BHist} :
    reflectiveStabilityFields (ReflectiveStabilityUp.mk S K A Q O F T L H C P N) =
        [S, K, A, Q, O, F, T, L, H, C, P, N] →
      Cont S T sourceAnchor →
        Cont K T checkpointAnchor →
          Cont A T auditAnchor →
            Cont O T observationAnchor →
              Cont F T interfaceAnchor →
                UnaryHistory S →
                  UnaryHistory K →
                    UnaryHistory A →
                      UnaryHistory O →
                        UnaryHistory F →
                          UnaryHistory T →
                            UnaryHistory sourceAnchor ∧
                              UnaryHistory checkpointAnchor ∧
                                UnaryHistory auditAnchor ∧
                                  UnaryHistory observationAnchor ∧
                                    UnaryHistory interfaceAnchor ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro _fields sTSource kTCheckpoint aTAudit oTObservation fTInterface
    sUnary kUnary aUnary oUnary fUnary tUnary
  exact
    ⟨unary_cont_closed sUnary tUnary sTSource,
      unary_cont_closed kUnary tUnary kTCheckpoint,
      unary_cont_closed aUnary tUnary aTAudit,
      unary_cont_closed oUnary tUnary oTObservation,
      unary_cont_closed fUnary tUnary fTInterface,
      hsame_refl N⟩

theorem ReflectiveStabilityCarrier_nonescape
    {S K A Q O F T L H C P N reuseRead ledgerRead finalTruth sourceIdentity hostValidation
      hiddenCheckpoint : BHist} :
    Cont Q C reuseRead ->
      Cont reuseRead T ledgerRead ->
        UnaryHistory Q ->
          UnaryHistory C ->
            UnaryHistory T ->
              reflectiveStabilityFields (ReflectiveStabilityUp.mk S K A Q O F T L H C P N) =
                  [S, K, A, Q, O, F, T, L, H, C, P, N] ->
                UnaryHistory reuseRead ∧ UnaryHistory ledgerRead ∧
                  hsame finalTruth finalTruth ∧ hsame sourceIdentity sourceIdentity ∧
                    hsame hostValidation hostValidation ∧
                      hsame hiddenCheckpoint hiddenCheckpoint := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro qCReuse reuseTLedger qUnary cUnary tUnary _fields
  have reuseUnary : UnaryHistory reuseRead :=
    unary_cont_closed qUnary cUnary qCReuse
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed reuseUnary tUnary reuseTLedger
  exact
    ⟨reuseUnary, ledgerUnary, hsame_refl finalTruth, hsame_refl sourceIdentity,
      hsame_refl hostValidation, hsame_refl hiddenCheckpoint⟩

end BEDC.Derived.ReflectiveStabilityUp
