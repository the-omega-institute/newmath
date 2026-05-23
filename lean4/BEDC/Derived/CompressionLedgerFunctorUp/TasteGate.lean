import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompressionLedgerFunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompressionLedgerFunctorUp : Type where
  | mk : (A K E R O M L Q J H C P N : BHist) → CompressionLedgerFunctorUp
  deriving DecidableEq

def compressionLedgerFunctorEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compressionLedgerFunctorEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compressionLedgerFunctorEncodeBHist h

def compressionLedgerFunctorDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compressionLedgerFunctorDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compressionLedgerFunctorDecodeBHist tail)

private theorem CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def compressionLedgerFunctorFields : CompressionLedgerFunctorUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N =>
      [A, K, E, R, O, M, L, Q, J, H, C, P, N]

def compressionLedgerFunctorToEventFlow : CompressionLedgerFunctorUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N =>
      [[BMark.b0],
        compressionLedgerFunctorEncodeBHist A,
        [BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist K,
        [BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist O,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        compressionLedgerFunctorEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist J,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        compressionLedgerFunctorEncodeBHist N]

private def CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault index rest

def compressionLedgerFunctorFromEventFlow
    (ef : EventFlow) : Option CompressionLedgerFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CompressionLedgerFunctorUp.mk
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 1 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 3 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 5 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 7 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 9 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 11 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 13 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 15 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 17 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 19 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 21 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 23 ef))
      (compressionLedgerFunctorDecodeBHist
        (CompressionLedgerFunctorTasteGate_single_carrier_alignment_eventAtDefault 25 ef)))

private theorem CompressionLedgerFunctorTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CompressionLedgerFunctorUp,
      compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow x) = some x :=
    by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A K E R O M L Q J H C P N =>
      change
        some
          (CompressionLedgerFunctorUp.mk
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist A))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist K))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist E))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist R))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist O))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist M))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist L))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist Q))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist J))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist H))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist C))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist P))
            (compressionLedgerFunctorDecodeBHist (compressionLedgerFunctorEncodeBHist N))) =
          some (CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N)
      rw [CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode A,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode K,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode E,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode R,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode O,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode M,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode L,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode Q,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode J,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode H,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode C,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode P,
        CompressionLedgerFunctorTasteGate_single_carrier_alignment_decode N]

private theorem CompressionLedgerFunctorToEventFlow_injective
    {x y : CompressionLedgerFunctorUp} :
    compressionLedgerFunctorToEventFlow x = compressionLedgerFunctorToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow x) =
        compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow y) :=
    congrArg compressionLedgerFunctorFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CompressionLedgerFunctorTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CompressionLedgerFunctorTasteGate_single_carrier_alignment_round_trip y)))

private theorem CompressionLedgerFunctorTasteGate_single_carrier_alignment_fields :
    ∀ x y : CompressionLedgerFunctorUp,
      compressionLedgerFunctorFields x = compressionLedgerFunctorFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A₁ K₁ E₁ R₁ O₁ M₁ L₁ Q₁ J₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk A₂ K₂ E₂ R₂ O₂ M₂ L₂ Q₂ J₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance compressionLedgerFunctorBHistCarrier : BHistCarrier CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compressionLedgerFunctorToEventFlow
  fromEventFlow := compressionLedgerFunctorFromEventFlow

instance compressionLedgerFunctorChapterTasteGate :
    ChapterTasteGate CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change compressionLedgerFunctorFromEventFlow (compressionLedgerFunctorToEventFlow x) = some x
    exact CompressionLedgerFunctorTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CompressionLedgerFunctorToEventFlow_injective heq)

instance compressionLedgerFunctorFieldFaithful : FieldFaithful CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compressionLedgerFunctorFields
  field_faithful := CompressionLedgerFunctorTasteGate_single_carrier_alignment_fields

instance compressionLedgerFunctorNontrivial : Nontrivial CompressionLedgerFunctorUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompressionLedgerFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      CompressionLedgerFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CompressionLedgerFunctorUp :=
  -- BEDC touchpoint anchor: BHist BMark
  compressionLedgerFunctorChapterTasteGate

theorem CompressionLedgerFunctorTasteGate_single_carrier_alignment :
    Nonempty (Nontrivial CompressionLedgerFunctorUp) ∧
      Nonempty (FieldFaithful CompressionLedgerFunctorUp) ∧
        Nonempty (ChapterTasteGate CompressionLedgerFunctorUp) ∧
          BHistCarrier.toEventFlow
              (CompressionLedgerFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty) ≠
            BHistCarrier.toEventFlow
              (CompressionLedgerFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact ⟨compressionLedgerFunctorNontrivial⟩
  · constructor
    · exact ⟨compressionLedgerFunctorFieldFaithful⟩
    · constructor
      · exact ⟨compressionLedgerFunctorChapterTasteGate⟩
      · intro heq
        have hxy :=
          CompressionLedgerFunctorToEventFlow_injective
            (x := CompressionLedgerFunctorUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
            (y := CompressionLedgerFunctorUp.mk (BHist.e0 BHist.Empty) BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
            heq
        cases hxy

theorem CompressionLedgerFunctorCarrier_namecert_obligations
    {A K E R O M L Q J H C P N alphaLedger betaLedger compositeLedger : BHist} :
    Cont M L alphaLedger ->
      Cont alphaLedger Q betaLedger ->
        Cont betaLedger J compositeLedger ->
          UnaryHistory M ->
            UnaryHistory L ->
              UnaryHistory Q ->
                UnaryHistory J ->
                  UnaryHistory alphaLedger ∧ UnaryHistory betaLedger ∧
                    UnaryHistory compositeLedger ∧
                    compressionLedgerFunctorFields
                        (CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N) =
                      [A, K, E, R, O, M, L, Q, J, H, C, P, N] ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row compositeLedger ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row compositeLedger ∧ Cont M L alphaLedger ∧
                          Cont alphaLedger Q betaLedger ∧ Cont betaLedger J compositeLedger)
                      (fun row : BHist =>
                        hsame row compositeLedger ∧
                          compressionLedgerFunctorFields
                              (CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N) =
                            [A, K, E, R, O, M, L, Q, J, H, C, P, N])
                      hsame := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont SemanticNameCert hsame
  intro mlAlpha alphaQBeta betaJComposite mUnary lUnary qUnary jUnary
  have alphaUnary : UnaryHistory alphaLedger :=
    unary_cont_closed mUnary lUnary mlAlpha
  have betaUnary : UnaryHistory betaLedger :=
    unary_cont_closed alphaUnary qUnary alphaQBeta
  have compositeUnary : UnaryHistory compositeLedger :=
    unary_cont_closed betaUnary jUnary betaJComposite
  have nameCert :
      SemanticNameCert
        (fun row : BHist => hsame row compositeLedger ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row compositeLedger ∧ Cont M L alphaLedger ∧
            Cont alphaLedger Q betaLedger ∧ Cont betaLedger J compositeLedger)
        (fun row : BHist =>
          hsame row compositeLedger ∧
            compressionLedgerFunctorFields
                (CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N) =
              [A, K, E, R, O, M, L, Q, J, H, C, P, N])
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro compositeLedger (And.intro (hsame_refl compositeLedger) compositeUnary)
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
      exact
        And.intro source.left
          (And.intro mlAlpha (And.intro alphaQBeta betaJComposite))
    ledger_sound := by
      intro _row source
      exact And.intro source.left rfl
  }
  exact ⟨alphaUnary, betaUnary, compositeUnary, rfl, nameCert⟩

theorem CompressionLedgerFunctorCarrier_composition_law
    {A K E R O M L Q J H C P N alphaLedger betaLedger compositeLedger
      routedComposite : BHist} :
    compressionLedgerFunctorFields (CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N) =
        [A, K, E, R, O, M, L, Q, J, H, C, P, N] →
      Cont M L alphaLedger →
        Cont alphaLedger Q betaLedger →
          Cont betaLedger J compositeLedger →
            Cont compositeLedger P routedComposite →
              UnaryHistory M →
                UnaryHistory L →
                  UnaryHistory Q →
                    UnaryHistory J →
                      UnaryHistory P →
                        UnaryHistory alphaLedger ∧
                          UnaryHistory betaLedger ∧
                            UnaryHistory compositeLedger ∧
                              UnaryHistory routedComposite ∧ hsame N N := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro _fields mlAlpha alphaQBeta betaJComposite compositePRouted
    mUnary lUnary qUnary jUnary pUnary
  have alphaUnary : UnaryHistory alphaLedger :=
    unary_cont_closed mUnary lUnary mlAlpha
  have betaUnary : UnaryHistory betaLedger :=
    unary_cont_closed alphaUnary qUnary alphaQBeta
  have compositeUnary : UnaryHistory compositeLedger :=
    unary_cont_closed betaUnary jUnary betaJComposite
  exact
    ⟨alphaUnary, betaUnary, compositeUnary,
      unary_cont_closed compositeUnary pUnary compositePRouted,
      hsame_refl N⟩

theorem CompressionLedgerFunctorCarrier_sibling_independence
    {A K E R O M L Q J H C P N alphaLedger betaLedger compositeLedger siblingProjection :
      BHist} :
    Cont M L alphaLedger ->
      Cont alphaLedger Q betaLedger ->
        Cont betaLedger J compositeLedger ->
          Cont siblingProjection H N ->
            UnaryHistory M ->
              UnaryHistory L ->
                UnaryHistory Q ->
                  UnaryHistory J ->
                    UnaryHistory H ->
                      compressionLedgerFunctorFields
                          (CompressionLedgerFunctorUp.mk A K E R O M L Q J H C P N) =
                        [A, K, E, R, O, M, L, Q, J, H, C, P, N] ->
                        UnaryHistory alphaLedger ∧ UnaryHistory betaLedger ∧
                          UnaryHistory compositeLedger ∧ hsame siblingProjection siblingProjection ∧
                            hsame N N := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro mlAlpha alphaQBeta betaJComposite _siblingHN
    mUnary lUnary qUnary jUnary _hUnary _fields
  have alphaUnary : UnaryHistory alphaLedger :=
    unary_cont_closed mUnary lUnary mlAlpha
  have betaUnary : UnaryHistory betaLedger :=
    unary_cont_closed alphaUnary qUnary alphaQBeta
  have compositeUnary : UnaryHistory compositeLedger :=
    unary_cont_closed betaUnary jUnary betaJComposite
  exact
    ⟨alphaUnary, betaUnary, compositeUnary, hsame_refl siblingProjection, hsame_refl N⟩

end BEDC.Derived.CompressionLedgerFunctorUp
