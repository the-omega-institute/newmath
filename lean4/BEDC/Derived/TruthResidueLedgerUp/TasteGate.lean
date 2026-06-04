import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TruthResidueLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TruthResidueLedgerUp : Type where
  | mk : (O I B P F G H C Q N : BHist) → TruthResidueLedgerUp
  deriving DecidableEq

def truthResidueLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: truthResidueLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: truthResidueLedgerEncodeBHist h

def truthResidueLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (truthResidueLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (truthResidueLedgerDecodeBHist tail)

private def truthResidueLedgerRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => truthResidueLedgerRawAt n rest

private theorem truthResidueLedger_decode_encode_bhist :
    ∀ h : BHist, truthResidueLedgerDecodeBHist (truthResidueLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem truthResidueLedger_mk_congr
    {O O' I I' B B' P P' F F' G G' H H' C C' Q Q' N N' : BHist}
    (hO : O' = O)
    (hI : I' = I)
    (hB : B' = B)
    (hP : P' = P)
    (hF : F' = F)
    (hG : G' = G)
    (hH : H' = H)
    (hC : C' = C)
    (hQ : Q' = Q)
    (hN : N' = N) :
    TruthResidueLedgerUp.mk O' I' B' P' F' G' H' C' Q' N' =
      TruthResidueLedgerUp.mk O I B P F G H C Q N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hO
  cases hI
  cases hB
  cases hP
  cases hF
  cases hG
  cases hH
  cases hC
  cases hQ
  cases hN
  rfl

def truthResidueLedgerFields : TruthResidueLedgerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TruthResidueLedgerUp.mk O I B P F G H C Q N =>
      [O, I, B, P, F, G, H, C, Q, N]

def truthResidueLedgerToEventFlow : TruthResidueLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TruthResidueLedgerUp.mk O I B P F G H C Q N =>
      [truthResidueLedgerEncodeBHist O,
        truthResidueLedgerEncodeBHist I,
        truthResidueLedgerEncodeBHist B,
        truthResidueLedgerEncodeBHist P,
        truthResidueLedgerEncodeBHist F,
        truthResidueLedgerEncodeBHist G,
        truthResidueLedgerEncodeBHist H,
        truthResidueLedgerEncodeBHist C,
        truthResidueLedgerEncodeBHist Q,
        truthResidueLedgerEncodeBHist N]

def truthResidueLedgerFromEventFlow (ef : EventFlow) : Option TruthResidueLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (TruthResidueLedgerUp.mk
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 0 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 1 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 2 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 3 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 4 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 5 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 6 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 7 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 8 ef))
      (truthResidueLedgerDecodeBHist (truthResidueLedgerRawAt 9 ef)))

private theorem truthResidueLedger_round_trip :
    ∀ x : TruthResidueLedgerUp,
      truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk O I B P F G H C Q N =>
      exact
        congrArg some
          (truthResidueLedger_mk_congr
            (truthResidueLedger_decode_encode_bhist O)
            (truthResidueLedger_decode_encode_bhist I)
            (truthResidueLedger_decode_encode_bhist B)
            (truthResidueLedger_decode_encode_bhist P)
            (truthResidueLedger_decode_encode_bhist F)
            (truthResidueLedger_decode_encode_bhist G)
            (truthResidueLedger_decode_encode_bhist H)
            (truthResidueLedger_decode_encode_bhist C)
            (truthResidueLedger_decode_encode_bhist Q)
            (truthResidueLedger_decode_encode_bhist N))

private theorem truthResidueLedgerToEventFlow_injective
    {x y : TruthResidueLedgerUp} :
    truthResidueLedgerToEventFlow x = truthResidueLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow x) =
        truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow y) :=
    congrArg truthResidueLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (truthResidueLedger_round_trip x).symm
      (Eq.trans hread (truthResidueLedger_round_trip y)))

private theorem truthResidueLedger_fields_faithful :
    ∀ x y : TruthResidueLedgerUp,
      truthResidueLedgerFields x = truthResidueLedgerFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk O₁ I₁ B₁ P₁ F₁ G₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk O₂ I₂ B₂ P₂ F₂ G₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance truthResidueLedgerBHistCarrier : BHistCarrier TruthResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := truthResidueLedgerToEventFlow
  fromEventFlow := truthResidueLedgerFromEventFlow

instance truthResidueLedgerChapterTasteGate :
    ChapterTasteGate TruthResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow x) = some x
    exact truthResidueLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (truthResidueLedgerToEventFlow_injective heq)

instance truthResidueLedgerFieldFaithful :
    FieldFaithful TruthResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := truthResidueLedgerFields
  field_faithful := truthResidueLedger_fields_faithful

instance truthResidueLedgerNontrivial :
    Nontrivial TruthResidueLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TruthResidueLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TruthResidueLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate TruthResidueLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  truthResidueLedgerChapterTasteGate

theorem TruthResidueLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist, truthResidueLedgerDecodeBHist (truthResidueLedgerEncodeBHist h) = h) ∧
      (∀ x : TruthResidueLedgerUp,
        truthResidueLedgerFromEventFlow (truthResidueLedgerToEventFlow x) = some x) ∧
        (∀ x y : TruthResidueLedgerUp,
          truthResidueLedgerToEventFlow x = truthResidueLedgerToEventFlow y → x = y) ∧
          truthResidueLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
            Nonempty (ChapterTasteGate TruthResidueLedgerUp) ∧
              Nonempty (FieldFaithful TruthResidueLedgerUp) ∧
                Nonempty (Nontrivial TruthResidueLedgerUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate Nontrivial
  exact
    ⟨truthResidueLedger_decode_encode_bhist,
      ⟨truthResidueLedger_round_trip,
        ⟨fun _x _y heq => truthResidueLedgerToEventFlow_injective heq,
          ⟨rfl,
            ⟨⟨truthResidueLedgerChapterTasteGate⟩,
              ⟨⟨truthResidueLedgerFieldFaithful⟩,
                ⟨truthResidueLedgerNontrivial⟩⟩⟩⟩⟩⟩⟩

theorem TruthResidueLedger_falsifiable_boundary
    (x : TruthResidueLedgerUp) :
    ∃ O I B P F G H C Q N : BHist,
      x = TruthResidueLedgerUp.mk O I B P F G H C Q N ∧
        truthResidueLedgerFields x = [O, I, B, P, F, G, H, C, Q, N] ∧
          Cont B P (append B P) ∧
            Cont I F (append I F) ∧
              Cont P N (append P N) ∧
                Cont F N (append F N) ∧
                  hsame G G := by
  -- BEDC touchpoint anchor: BHist Cont hsame
  cases x with
  | mk O I B P F G H C Q N =>
      exact
        ⟨O, I, B, P, F, G, H, C, Q, N, rfl, rfl, cont_intro rfl,
          cont_intro rfl, cont_intro rfl, cont_intro rfl, hsame_refl G⟩

theorem TruthResidueLedger_namecert_obligations
    {O I B P F G H C Q N obsRead invariantRead bridgeRead predictionRead
      falsificationRead nonfinalRead : BHist} :
    truthResidueLedgerFields (TruthResidueLedgerUp.mk O I B P F G H C Q N) =
        [O, I, B, P, F, G, H, C, Q, N] →
      UnaryHistory O →
        UnaryHistory I →
          UnaryHistory B →
            UnaryHistory P →
              UnaryHistory F →
                UnaryHistory G →
                  UnaryHistory N →
                    Cont O I obsRead →
                      Cont obsRead B invariantRead →
                        Cont invariantRead P bridgeRead →
                          Cont bridgeRead F predictionRead →
                            Cont predictionRead G falsificationRead →
                              Cont falsificationRead N nonfinalRead →
                                SemanticNameCert
                                  (fun row : BHist => hsame row nonfinalRead ∧ UnaryHistory row)
                                  (fun row : BHist =>
                                    hsame row O ∨ hsame row I ∨ hsame row B ∨
                                      hsame row P ∨ hsame row F ∨ hsame row G ∨
                                        hsame row H ∨ hsame row C ∨ hsame row Q ∨
                                          hsame row N ∨ hsame row nonfinalRead)
                                  (fun row : BHist =>
                                    UnaryHistory row ∧ Cont O I obsRead ∧
                                      Cont obsRead B invariantRead ∧
                                        Cont invariantRead P bridgeRead ∧
                                          Cont bridgeRead F predictionRead ∧
                                            Cont predictionRead G falsificationRead ∧
                                              Cont falsificationRead N nonfinalRead)
                                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory NameCert
  intro _fields uO uI uB uP uF uG uN cOI cObsB cInvP cBridgeF cPredG cFalsN
  have uObs : UnaryHistory obsRead :=
    unary_cont_closed uO uI cOI
  have uInvariant : UnaryHistory invariantRead :=
    unary_cont_closed uObs uB cObsB
  have uBridge : UnaryHistory bridgeRead :=
    unary_cont_closed uInvariant uP cInvP
  have uPrediction : UnaryHistory predictionRead :=
    unary_cont_closed uBridge uF cBridgeF
  have uFalsification : UnaryHistory falsificationRead :=
    unary_cont_closed uPrediction uG cPredG
  have uNonfinal : UnaryHistory nonfinalRead :=
    unary_cont_closed uFalsification uN cFalsN
  constructor
  · constructor
    · exact ⟨nonfinalRead, ⟨hsame_refl nonfinalRead, uNonfinal⟩⟩
    · intro row source
      exact hsame_refl row
    · intro row col same
      exact hsame_symm same
    · intro row col next sameRow sameNext
      exact hsame_trans sameRow sameNext
    · intro row col same source
      cases same
      exact source
  · intro row source
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))))))
  · intro row source
    exact
      ⟨source.right,
        ⟨cOI,
          ⟨cObsB,
            ⟨cInvP,
              ⟨cBridgeF,
                ⟨cPredG, cFalsN⟩⟩⟩⟩⟩⟩

end BEDC.Derived.TruthResidueLedgerUp
