import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedSequenceSupremumUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedSequenceSupremumUp : Type where
  | mk
      (B W R L U E H C P N : BHist) :
      LocatedSequenceSupremumUp
  deriving DecidableEq

def locatedSequenceSupremumEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedSequenceSupremumEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedSequenceSupremumEncodeBHist h

def locatedSequenceSupremumDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedSequenceSupremumDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedSequenceSupremumDecodeBHist tail)

private theorem LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedSequenceSupremumToEventFlow : LocatedSequenceSupremumUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSequenceSupremumUp.mk B W R L U E H C P N =>
      [[BMark.b1, BMark.b1, BMark.b0, BMark.b1],
        locatedSequenceSupremumEncodeBHist B,
        locatedSequenceSupremumEncodeBHist W,
        locatedSequenceSupremumEncodeBHist R,
        locatedSequenceSupremumEncodeBHist L,
        locatedSequenceSupremumEncodeBHist U,
        locatedSequenceSupremumEncodeBHist E,
        locatedSequenceSupremumEncodeBHist H,
        locatedSequenceSupremumEncodeBHist C,
        locatedSequenceSupremumEncodeBHist P,
        locatedSequenceSupremumEncodeBHist N]

def locatedSequenceSupremumFields : LocatedSequenceSupremumUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedSequenceSupremumUp.mk B W R L U E H C P N => [B, W, R, L, U, E, H, C, P, N]

def locatedSequenceSupremumFromEventFlow : EventFlow → Option LocatedSequenceSupremumUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: restB =>
      match restB with
      | [] => none
      | B :: restW =>
          match restW with
          | [] => none
          | W :: restR =>
              match restR with
              | [] => none
              | R :: restL =>
                  match restL with
                  | [] => none
                  | L :: restU =>
                      match restU with
                      | [] => none
                      | U :: restE =>
                          match restE with
                          | [] => none
                          | E :: restH =>
                              match restH with
                              | [] => none
                              | H :: restC =>
                                  match restC with
                                  | [] => none
                                  | C :: restP =>
                                      match restP with
                                      | [] => none
                                      | P :: restN =>
                                          match restN with
                                          | [] => none
                                          | N :: rest =>
                                              match rest with
                                              | [] =>
                                                  some
                                                    (LocatedSequenceSupremumUp.mk
                                                      (locatedSequenceSupremumDecodeBHist B)
                                                      (locatedSequenceSupremumDecodeBHist W)
                                                      (locatedSequenceSupremumDecodeBHist R)
                                                      (locatedSequenceSupremumDecodeBHist L)
                                                      (locatedSequenceSupremumDecodeBHist U)
                                                      (locatedSequenceSupremumDecodeBHist E)
                                                      (locatedSequenceSupremumDecodeBHist H)
                                                      (locatedSequenceSupremumDecodeBHist C)
                                                      (locatedSequenceSupremumDecodeBHist P)
                                                      (locatedSequenceSupremumDecodeBHist N))
                                              | _ :: _ => none

private theorem LocatedSequenceSupremumTasteGate_single_carrier_alignment_round_trip :
    ∀ x : LocatedSequenceSupremumUp,
      locatedSequenceSupremumFromEventFlow (locatedSequenceSupremumToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk B W R L U E H C P N =>
      change
        some
          (LocatedSequenceSupremumUp.mk
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist B))
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist W))
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist R))
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist L))
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist U))
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist E))
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist H))
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist C))
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist P))
            (locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist N))) =
          some (LocatedSequenceSupremumUp.mk B W R L U E H C P N)
      rw [LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode B,
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode W,
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode R,
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode L,
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode U,
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode E,
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode H,
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode C,
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode P,
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode N]

private theorem LocatedSequenceSupremumTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LocatedSequenceSupremumUp} :
    locatedSequenceSupremumToEventFlow x = locatedSequenceSupremumToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedSequenceSupremumFromEventFlow (locatedSequenceSupremumToEventFlow x) =
        locatedSequenceSupremumFromEventFlow (locatedSequenceSupremumToEventFlow y) :=
    congrArg locatedSequenceSupremumFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (LocatedSequenceSupremumTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (LocatedSequenceSupremumTasteGate_single_carrier_alignment_round_trip y)))

instance locatedSequenceSupremumBHistCarrier : BHistCarrier LocatedSequenceSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedSequenceSupremumToEventFlow
  fromEventFlow := locatedSequenceSupremumFromEventFlow

instance locatedSequenceSupremumChapterTasteGate :
    ChapterTasteGate LocatedSequenceSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      locatedSequenceSupremumFromEventFlow (locatedSequenceSupremumToEventFlow x) =
        some x
    exact LocatedSequenceSupremumTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (LocatedSequenceSupremumTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance locatedSequenceSupremumFieldFaithful :
    FieldFaithful LocatedSequenceSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | LocatedSequenceSupremumUp.mk B W R L U E H C P N => [B, W, R, L, U, E, H, C, P, N]
  field_faithful := by
    intro x y h
    cases x with
    | mk B₁ W₁ R₁ L₁ U₁ E₁ H₁ C₁ P₁ N₁ =>
        cases y with
        | mk B₂ W₂ R₂ L₂ U₂ E₂ H₂ C₂ P₂ N₂ =>
            injection h with hB tB
            injection tB with hW tW
            injection tW with hR tR
            injection tR with hL tL
            injection tL with hU tU
            injection tU with hE tE
            injection tE with hH tH
            injection tH with hC tC
            injection tC with hP tP
            injection tP with hN _
            subst hB
            subst hW
            subst hR
            subst hL
            subst hU
            subst hE
            subst hH
            subst hC
            subst hP
            subst hN
            rfl

instance locatedSequenceSupremumNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedSequenceSupremumUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedSequenceSupremumUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedSequenceSupremumUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem LocatedSequenceSupremumTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedSequenceSupremumDecodeBHist (locatedSequenceSupremumEncodeBHist h) = h) ∧
      (∀ x : LocatedSequenceSupremumUp,
        locatedSequenceSupremumFromEventFlow (locatedSequenceSupremumToEventFlow x) =
          some x) ∧
        (∀ x y : LocatedSequenceSupremumUp,
          locatedSequenceSupremumToEventFlow x =
            locatedSequenceSupremumToEventFlow y → x = y) ∧
          locatedSequenceSupremumEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨LocatedSequenceSupremumTasteGate_single_carrier_alignment_decode_encode,
      LocatedSequenceSupremumTasteGate_single_carrier_alignment_round_trip,
      fun _ _ heq =>
        LocatedSequenceSupremumTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

theorem LocatedSequenceSupremumCarrier_namecert_obligations
    (x : LocatedSequenceSupremumUp) :
    ∃ localCert : BHist,
      SemanticNameCert
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ locatedSequenceSupremumFields x)
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ locatedSequenceSupremumFields x)
        (fun row : BHist =>
          hsame row localCert ∧ localCert ∈ locatedSequenceSupremumFields x)
        hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert NameCert
  cases x with
  | mk B W R L U E H C P N =>
      refine ⟨N, ?_⟩
      refine
        { core :=
            { carrier_inhabited := ?_
              equiv_refl := ?_
              equiv_symm := ?_
              equiv_trans := ?_
              carrier_respects_equiv := ?_ }
          pattern_sound := ?_
          ledger_sound := ?_ }
      · exact
          ⟨N, hsame_refl N,
            List.Mem.tail _ <|
              List.Mem.tail _ <|
                List.Mem.tail _ <|
                  List.Mem.tail _ <|
                    List.Mem.tail _ <|
                      List.Mem.tail _ <|
                        List.Mem.tail _ <|
                          List.Mem.tail _ <|
                            List.Mem.tail _ <| List.Mem.head _⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _other _third same₁ same₂
        exact hsame_trans same₁ same₂
      · intro _row _other same source
        exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
      · intro _row source
        exact source
      · intro _row source
        exact source

end BEDC.Derived.LocatedSequenceSupremumUp
