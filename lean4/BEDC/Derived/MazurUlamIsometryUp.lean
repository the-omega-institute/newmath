import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MazurUlamIsometryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MazurUlamIsometryUp : Type where
  | mk : (E F G M A H C P N : BHist) → MazurUlamIsometryUp
  deriving DecidableEq

def mazurUlamIsometryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: mazurUlamIsometryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: mazurUlamIsometryEncodeBHist h

def mazurUlamIsometryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (mazurUlamIsometryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (mazurUlamIsometryDecodeBHist tail)

private theorem mazurUlamIsometry_decode_encode_bhist :
    ∀ h : BHist,
      mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def mazurUlamIsometryToEventFlow : MazurUlamIsometryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MazurUlamIsometryUp.mk E F G M A H C P N =>
      [[BMark.b0],
        mazurUlamIsometryEncodeBHist E,
        [BMark.b1, BMark.b0],
        mazurUlamIsometryEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b0],
        mazurUlamIsometryEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mazurUlamIsometryEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mazurUlamIsometryEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mazurUlamIsometryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        mazurUlamIsometryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        mazurUlamIsometryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        mazurUlamIsometryEncodeBHist N]

def mazurUlamIsometryFromEventFlow : EventFlow → Option MazurUlamIsometryUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | E :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | F :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | G :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | M :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | A :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | H :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | C :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | P :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | N :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (MazurUlamIsometryUp.mk
                                                                                  (mazurUlamIsometryDecodeBHist E)
                                                                                  (mazurUlamIsometryDecodeBHist F)
                                                                                  (mazurUlamIsometryDecodeBHist G)
                                                                                  (mazurUlamIsometryDecodeBHist M)
                                                                                  (mazurUlamIsometryDecodeBHist A)
                                                                                  (mazurUlamIsometryDecodeBHist H)
                                                                                  (mazurUlamIsometryDecodeBHist C)
                                                                                  (mazurUlamIsometryDecodeBHist P)
                                                                                  (mazurUlamIsometryDecodeBHist N))
                                                                          | _ :: _ => none

private theorem mazurUlamIsometry_round_trip :
    ∀ x : MazurUlamIsometryUp,
      mazurUlamIsometryFromEventFlow (mazurUlamIsometryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk E F G M A H C P N =>
      change
        some
          (MazurUlamIsometryUp.mk
            (mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist E))
            (mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist F))
            (mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist G))
            (mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist M))
            (mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist A))
            (mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist H))
            (mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist C))
            (mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist P))
            (mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist N))) =
          some (MazurUlamIsometryUp.mk E F G M A H C P N)
      rw [mazurUlamIsometry_decode_encode_bhist E,
        mazurUlamIsometry_decode_encode_bhist F,
        mazurUlamIsometry_decode_encode_bhist G,
        mazurUlamIsometry_decode_encode_bhist M,
        mazurUlamIsometry_decode_encode_bhist A,
        mazurUlamIsometry_decode_encode_bhist H,
        mazurUlamIsometry_decode_encode_bhist C,
        mazurUlamIsometry_decode_encode_bhist P,
        mazurUlamIsometry_decode_encode_bhist N]

private theorem mazurUlamIsometryToEventFlow_injective {x y : MazurUlamIsometryUp} :
    mazurUlamIsometryToEventFlow x = mazurUlamIsometryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      mazurUlamIsometryFromEventFlow (mazurUlamIsometryToEventFlow x) =
        mazurUlamIsometryFromEventFlow (mazurUlamIsometryToEventFlow y) :=
    congrArg mazurUlamIsometryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (mazurUlamIsometry_round_trip x).symm
      (Eq.trans hread (mazurUlamIsometry_round_trip y)))

instance mazurUlamIsometryBHistCarrier : BHistCarrier MazurUlamIsometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := mazurUlamIsometryToEventFlow
  fromEventFlow := mazurUlamIsometryFromEventFlow

instance mazurUlamIsometryChapterTasteGate :
    ChapterTasteGate MazurUlamIsometryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change mazurUlamIsometryFromEventFlow (mazurUlamIsometryToEventFlow x) = some x
    exact mazurUlamIsometry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (mazurUlamIsometryToEventFlow_injective heq)

def MazurUlamIsometryCarrier [AskSetup] [PackageSetup]
    (E F G M A H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory E ∧ UnaryHistory F ∧ UnaryHistory G ∧ UnaryHistory M ∧
    UnaryHistory A ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg

theorem MazurUlamIsometryCarrier_midpoint_preservation [AskSetup] [PackageSetup]
    {E F G M A H C P N midpointRead targetRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MazurUlamIsometryCarrier E F G M A H C P N bundle pkg ->
      Cont G M midpointRead ->
        Cont midpointRead H targetRead ->
          PkgSig bundle P pkg ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row G ∨ hsame row M ∨ hsame row midpointRead ∨
                    hsame row targetRead) ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row E ∨ hsame row F ∨ hsame row G ∨ hsame row M ∨
                    hsame row A ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N ∨ hsame row midpointRead ∨ hsame row targetRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont G M midpointRead ∧
                    Cont midpointRead H targetRead ∧ PkgSig bundle P pkg)
                hsame ∧
              UnaryHistory midpointRead ∧ UnaryHistory targetRead := by
  -- BEDC touchpoint anchor: MazurUlamIsometryCarrier BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier midpointRoute targetRoute provenancePkg
  obtain ⟨_eUnary, _fUnary, gUnary, mUnary, _aUnary, hUnary, _cUnary, _pUnary,
    _nUnary, _carrierPkg⟩ := carrier
  have midpointUnary : UnaryHistory midpointRead :=
    unary_cont_closed gUnary mUnary midpointRoute
  have targetUnary : UnaryHistory targetRead :=
    unary_cont_closed midpointUnary hUnary targetRoute
  have source :
      (fun row : BHist =>
        (hsame row G ∨ hsame row M ∨ hsame row midpointRead ∨ hsame row targetRead) ∧
          UnaryHistory row) midpointRead := by
    exact ⟨Or.inr (Or.inr (Or.inl (hsame_refl midpointRead))), midpointUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row G ∨ hsame row M ∨ hsame row midpointRead ∨ hsame row targetRead) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row E ∨ hsame row F ∨ hsame row G ∨ hsame row M ∨ hsame row A ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row midpointRead ∨ hsame row targetRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G M midpointRead ∧ Cont midpointRead H targetRead ∧
              PkgSig bundle P pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro midpointRead source
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
          intro _row _other sameRows sourceRows
          constructor
          · cases sourceRows.left with
            | inl sameG =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) sameG)
            | inr rest =>
                cases rest with
                | inl sameM =>
                    exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameM))
                | inr rest =>
                    cases rest with
                    | inl sameMidpoint =>
                        exact
                          Or.inr
                            (Or.inr
                              (Or.inl (hsame_trans (hsame_symm sameRows) sameMidpoint)))
                    | inr sameTarget =>
                        exact
                          Or.inr
                            (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameTarget)))
          · exact unary_transport sourceRows.right sameRows
      }
      pattern_sound := by
        intro _row sourceRows
        cases sourceRows.left with
        | inl sameG =>
            exact Or.inr (Or.inr (Or.inl sameG))
        | inr rest =>
            cases rest with
            | inl sameM =>
                exact Or.inr (Or.inr (Or.inr (Or.inl sameM)))
            | inr rest =>
                cases rest with
                | inl sameMidpoint =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inl sameMidpoint)))))))))
                | inr sameTarget =>
                    exact
                      Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr
                                (Or.inr
                                  (Or.inr
                                    (Or.inr
                                      (Or.inr (Or.inr sameTarget)))))))))
      ledger_sound := by
        intro _row sourceRows
        exact ⟨sourceRows.right, midpointRoute, targetRoute, provenancePkg⟩
    }
  exact ⟨cert, midpointUnary, targetUnary⟩

theorem MazurUlamIsometryTasteGate_single_carrier_alignment :
    (∀ h : BHist, mazurUlamIsometryDecodeBHist (mazurUlamIsometryEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MazurUlamIsometryUp) ∧
        Nonempty (ChapterTasteGate MazurUlamIsometryUp) ∧
          mazurUlamIsometryEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact mazurUlamIsometry_decode_encode_bhist
  · constructor
    · exact ⟨mazurUlamIsometryBHistCarrier⟩
    · constructor
      · exact ⟨mazurUlamIsometryChapterTasteGate⟩
      · rfl

end BEDC.Derived.MazurUlamIsometryUp
