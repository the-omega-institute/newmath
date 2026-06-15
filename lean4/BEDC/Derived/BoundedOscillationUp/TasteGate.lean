import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BoundedOscillationUp.TasteGate

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BoundedOscillationUp : Type where
  | mk (I W R D L B S H C P N : BHist) : BoundedOscillationUp
  deriving DecidableEq

def boundedOscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: boundedOscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: boundedOscillationEncodeBHist h

def boundedOscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (boundedOscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (boundedOscillationDecodeBHist tail)

private theorem boundedOscillation_decode_encode :
    ∀ h : BHist, boundedOscillationDecodeBHist (boundedOscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def boundedOscillationFields : BoundedOscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BoundedOscillationUp.mk I W R D L B S H C P N => [I, W, R, D, L, B, S, H, C, P, N]

def boundedOscillationToEventFlow : BoundedOscillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (boundedOscillationFields token).map boundedOscillationEncodeBHist

def boundedOscillationFromEventFlow : EventFlow → Option BoundedOscillationUp
  -- BEDC touchpoint anchor: BHist BMark
  | I :: restI =>
      match restI with
      | W :: restW =>
          match restW with
          | R :: restR =>
              match restR with
              | D :: restD =>
                  match restD with
                  | L :: restL =>
                      match restL with
                      | B :: restB =>
                          match restB with
                          | S :: restS =>
                              match restS with
                              | H :: restH =>
                                  match restH with
                                  | C :: restC =>
                                      match restC with
                                      | P :: restP =>
                                          match restP with
                                          | N :: restN =>
                                              match restN with
                                              | [] =>
                                                  some
                                                    (BoundedOscillationUp.mk
                                                      (boundedOscillationDecodeBHist I)
                                                      (boundedOscillationDecodeBHist W)
                                                      (boundedOscillationDecodeBHist R)
                                                      (boundedOscillationDecodeBHist D)
                                                      (boundedOscillationDecodeBHist L)
                                                      (boundedOscillationDecodeBHist B)
                                                      (boundedOscillationDecodeBHist S)
                                                      (boundedOscillationDecodeBHist H)
                                                      (boundedOscillationDecodeBHist C)
                                                      (boundedOscillationDecodeBHist P)
                                                      (boundedOscillationDecodeBHist N))
                                              | _ :: _ => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem boundedOscillation_round_trip :
    ∀ token : BoundedOscillationUp,
      boundedOscillationFromEventFlow (boundedOscillationToEventFlow token) = some token := by
  -- BEDC touchpoint anchor: BHist BMark
  intro token
  cases token with
  | mk I W R D L B S H C P N =>
      change
        some
            (BoundedOscillationUp.mk
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist I))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist W))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist R))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist D))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist L))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist B))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist S))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist H))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist C))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist P))
              (boundedOscillationDecodeBHist (boundedOscillationEncodeBHist N))) =
          some (BoundedOscillationUp.mk I W R D L B S H C P N)
      rw [boundedOscillation_decode_encode I]
      rw [boundedOscillation_decode_encode W]
      rw [boundedOscillation_decode_encode R]
      rw [boundedOscillation_decode_encode D]
      rw [boundedOscillation_decode_encode L]
      rw [boundedOscillation_decode_encode B]
      rw [boundedOscillation_decode_encode S]
      rw [boundedOscillation_decode_encode H]
      rw [boundedOscillation_decode_encode C]
      rw [boundedOscillation_decode_encode P]
      rw [boundedOscillation_decode_encode N]

private theorem boundedOscillationToEventFlow_injective {x y : BoundedOscillationUp} :
    boundedOscillationToEventFlow x = boundedOscillationToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      boundedOscillationFromEventFlow (boundedOscillationToEventFlow x) =
        boundedOscillationFromEventFlow (boundedOscillationToEventFlow y) :=
    congrArg boundedOscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (boundedOscillation_round_trip x).symm
      (Eq.trans hread (boundedOscillation_round_trip y)))

instance boundedOscillationBHistCarrier : BHistCarrier BoundedOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := boundedOscillationToEventFlow
  fromEventFlow := boundedOscillationFromEventFlow

instance boundedOscillationChapterTasteGate : ChapterTasteGate BoundedOscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change boundedOscillationFromEventFlow (boundedOscillationToEventFlow x) = some x
    exact boundedOscillation_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (boundedOscillationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate BoundedOscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  boundedOscillationChapterTasteGate

theorem BoundedOscillationTasteGate_single_carrier_alignment :
    (forall h : BHist, boundedOscillationDecodeBHist (boundedOscillationEncodeBHist h) = h) ∧
      (forall x : BoundedOscillationUp,
        boundedOscillationFromEventFlow (boundedOscillationToEventFlow x) = some x) ∧
        (forall x y : BoundedOscillationUp,
          boundedOscillationToEventFlow x = boundedOscillationToEventFlow y -> x = y) ∧
          boundedOscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨boundedOscillation_decode_encode, boundedOscillation_round_trip,
      (by
        intro x y heq
        exact boundedOscillationToEventFlow_injective heq),
      rfl⟩

theorem BoundedOscillationNamecertObligations (O : BoundedOscillationUp) :
    ∃ I W R D L B S H C P N : BHist,
      O = BoundedOscillationUp.mk I W R D L B S H C P N ∧
        SemanticNameCert
          (fun row : BHist =>
            hsame row I ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row L ∨
              hsame row B ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist =>
            hsame row I ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row L ∨
              hsame row B ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist =>
            hsame row I ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row L ∨
              hsame row B ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          hsame := by
  -- BEDC touchpoint anchor: BHist hsame SemanticNameCert
  cases O with
  | mk I W R D L B S H C P N =>
      let rows := fun row : BHist =>
        hsame row I ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨ hsame row L ∨
          hsame row B ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
            hsame row N
      have cert : SemanticNameCert rows rows rows hsame := {
        core := {
          carrier_inhabited := Exists.intro I (Or.inl (hsame_refl I))
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
            intro _row _other sameRows source
            cases sameRows
            exact source
        }
        pattern_sound := by
          intro _row source
          exact source
        ledger_sound := by
          intro _row source
          exact source
      }
      exact ⟨I, W, R, D, L, B, S, H, C, P, N, rfl, cert⟩

theorem BoundedOscillationDarbouxHandoff
    {I W R D L B S H C P N windowRead readbackRead ledgerRead boundedRead
      darbouxRead : BHist} :
    Cont I W windowRead →
      Cont windowRead R readbackRead →
        Cont D L ledgerRead →
          Cont ledgerRead B boundedRead →
            Cont boundedRead S darbouxRead →
              SemanticNameCert
                (fun row : BHist => hsame row darbouxRead)
                (fun row : BHist =>
                  hsame row I ∨ hsame row W ∨ hsame row R ∨ hsame row D ∨
                    hsame row L ∨ hsame row B ∨ hsame row S ∨ hsame row darbouxRead)
                (fun row : BHist =>
                  Cont I W windowRead ∧ Cont windowRead R readbackRead ∧
                    Cont D L ledgerRead ∧ Cont ledgerRead B boundedRead ∧
                      Cont boundedRead S darbouxRead ∧ hsame row darbouxRead)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  intro windowRoute readbackRoute ledgerRoute boundedRoute darbouxRoute
  refine
    { core :=
        { carrier_inhabited := ?carrier_inhabited
          equiv_refl := ?equiv_refl
          equiv_symm := ?equiv_symm
          equiv_trans := ?equiv_trans
          carrier_respects_equiv := ?carrier_respects_equiv }
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · exact ⟨darbouxRead, hsame_refl darbouxRead⟩
  · intro row _source
    exact hsame_refl row
  · intro _row _other same
    exact hsame_symm same
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other same source
    exact hsame_trans (hsame_symm same) source
  · intro _row source
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source))))))
  · intro _row source
    exact
      ⟨windowRoute, readbackRoute, ledgerRoute, boundedRoute, darbouxRoute, source⟩

end BEDC.Derived.BoundedOscillationUp.TasteGate
