import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BorelSetUp

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

inductive BorelSetUp : Type where
  | mk (X O M G R H C P N : BHist) : BorelSetUp
  deriving DecidableEq

def borelSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: borelSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: borelSetEncodeBHist h

def borelSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (borelSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (borelSetDecodeBHist tail)

private theorem BorelSetTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, borelSetDecodeBHist (borelSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def BorelSetTasteGate_single_carrier_alignment_fields : BorelSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BorelSetUp.mk X O M G R H C P N => [X, O, M, G, R, H, C, P, N]

def BorelSetTasteGate_single_carrier_alignment_toEventFlow : BorelSetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (BorelSetTasteGate_single_carrier_alignment_fields x).map borelSetEncodeBHist

private def BorelSetTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => BorelSetTasteGate_single_carrier_alignment_eventAt index rest

def BorelSetTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option BorelSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BorelSetUp.mk
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 0 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 1 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 2 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 3 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 4 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 5 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 6 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 7 ef))
      (borelSetDecodeBHist (BorelSetTasteGate_single_carrier_alignment_eventAt 8 ef)))

private theorem BorelSetTasteGate_single_carrier_alignment_round_trip
    (x : BorelSetUp) :
    BorelSetTasteGate_single_carrier_alignment_fromEventFlow
        (BorelSetTasteGate_single_carrier_alignment_toEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk X O M G R H C P N =>
      change
        some
          (BorelSetUp.mk
            (borelSetDecodeBHist (borelSetEncodeBHist X))
            (borelSetDecodeBHist (borelSetEncodeBHist O))
            (borelSetDecodeBHist (borelSetEncodeBHist M))
            (borelSetDecodeBHist (borelSetEncodeBHist G))
            (borelSetDecodeBHist (borelSetEncodeBHist R))
            (borelSetDecodeBHist (borelSetEncodeBHist H))
            (borelSetDecodeBHist (borelSetEncodeBHist C))
            (borelSetDecodeBHist (borelSetEncodeBHist P))
            (borelSetDecodeBHist (borelSetEncodeBHist N))) =
          some (BorelSetUp.mk X O M G R H C P N)
      rw [BorelSetTasteGate_single_carrier_alignment_decode_encode X,
        BorelSetTasteGate_single_carrier_alignment_decode_encode O,
        BorelSetTasteGate_single_carrier_alignment_decode_encode M,
        BorelSetTasteGate_single_carrier_alignment_decode_encode G,
        BorelSetTasteGate_single_carrier_alignment_decode_encode R,
        BorelSetTasteGate_single_carrier_alignment_decode_encode H,
        BorelSetTasteGate_single_carrier_alignment_decode_encode C,
        BorelSetTasteGate_single_carrier_alignment_decode_encode P,
        BorelSetTasteGate_single_carrier_alignment_decode_encode N]

private theorem BorelSetTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BorelSetUp} :
    BorelSetTasteGate_single_carrier_alignment_toEventFlow x =
        BorelSetTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      BorelSetTasteGate_single_carrier_alignment_fromEventFlow
          (BorelSetTasteGate_single_carrier_alignment_toEventFlow x) =
        BorelSetTasteGate_single_carrier_alignment_fromEventFlow
          (BorelSetTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg BorelSetTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (BorelSetTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BorelSetTasteGate_single_carrier_alignment_round_trip y)))

instance BorelSetTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier BorelSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := BorelSetTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := BorelSetTasteGate_single_carrier_alignment_fromEventFlow

instance BorelSetTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate BorelSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      BorelSetTasteGate_single_carrier_alignment_fromEventFlow
          (BorelSetTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact BorelSetTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BorelSetTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem BorelSetTasteGate_single_carrier_alignment :
    (∀ h : BHist, borelSetDecodeBHist (borelSetEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier BorelSetUp) ∧
        Nonempty (ChapterTasteGate BorelSetUp) ∧
          borelSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨BorelSetTasteGate_single_carrier_alignment_decode_encode,
      ⟨⟨BorelSetTasteGate_single_carrier_alignment_BHistCarrier⟩,
        ⟨⟨BorelSetTasteGate_single_carrier_alignment_ChapterTasteGate⟩, rfl⟩⟩⟩

def BorelSetCarrier [AskSetup] [PackageSetup]
    (X O M G R H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory O ∧ UnaryHistory M ∧ UnaryHistory G ∧
    UnaryHistory R ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem BorelSetCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X O M G R H C P N sourceRead generatorRead membershipRead readbackRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BorelSetCarrier X O M G R H C P N bundle pkg ->
      Cont X O sourceRead ->
        Cont O G generatorRead ->
          Cont M R membershipRead ->
            Cont generatorRead membershipRead readbackRead ->
              PkgSig bundle readbackRead pkg ->
                SemanticNameCert
                    (fun row : BHist =>
                      (hsame row sourceRead ∨ hsame row generatorRead ∨
                        hsame row membershipRead ∨ hsame row readbackRead ∨
                          hsame row X ∨ hsame row O ∨ hsame row M ∨
                            hsame row G ∨ hsame row R) ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row O ∨ hsame row M ∨ hsame row G ∨
                        hsame row R ∨ hsame row sourceRead ∨
                          hsame row generatorRead ∨ hsame row membershipRead ∨
                            hsame row readbackRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle readbackRead pkg ∧
                        PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory sourceRead ∧ UnaryHistory generatorRead ∧
                    UnaryHistory membershipRead ∧ UnaryHistory readbackRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sourceRoute generatorRoute membershipRoute readbackRoute readbackPkg
  obtain ⟨xUnary, oUnary, mUnary, gUnary, rUnary, _hUnary, _cUnary, _pUnary,
    _nUnary, provenancePkg, _namePkg⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed xUnary oUnary sourceRoute
  have generatorUnary : UnaryHistory generatorRead :=
    unary_cont_closed oUnary gUnary generatorRoute
  have membershipUnary : UnaryHistory membershipRead :=
    unary_cont_closed mUnary rUnary membershipRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed generatorUnary membershipUnary readbackRoute
  have sourceWitness :
      (fun row : BHist =>
        (hsame row sourceRead ∨ hsame row generatorRead ∨
          hsame row membershipRead ∨ hsame row readbackRead ∨ hsame row X ∨
            hsame row O ∨ hsame row M ∨ hsame row G ∨ hsame row R) ∧
          UnaryHistory row) readbackRead := by
    exact
      ⟨Or.inr (Or.inr (Or.inr (Or.inl (hsame_refl readbackRead)))),
        readbackUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row sourceRead ∨ hsame row generatorRead ∨
              hsame row membershipRead ∨ hsame row readbackRead ∨ hsame row X ∨
                hsame row O ∨ hsame row M ∨ hsame row G ∨ hsame row R) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row O ∨ hsame row M ∨ hsame row G ∨
              hsame row R ∨ hsame row sourceRead ∨ hsame row generatorRead ∨
                hsame row membershipRead ∨ hsame row readbackRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle readbackRead pkg ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readbackRead sourceWitness
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
        constructor
        · cases source.left with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm sameRows) sameSource)
          | inr rest =>
              cases rest with
              | inl sameGenerator =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameGenerator))
              | inr rest =>
                  cases rest with
                  | inl sameMembership =>
                      exact Or.inr (Or.inr
                        (Or.inl (hsame_trans (hsame_symm sameRows) sameMembership)))
                  | inr rest =>
                      cases rest with
                      | inl sameReadback =>
                          exact Or.inr (Or.inr (Or.inr
                            (Or.inl (hsame_trans (hsame_symm sameRows) sameReadback))))
                      | inr rest =>
                          cases rest with
                          | inl sameX =>
                              exact Or.inr (Or.inr (Or.inr (Or.inr
                                (Or.inl (hsame_trans (hsame_symm sameRows) sameX)))))
                          | inr rest =>
                              cases rest with
                              | inl sameO =>
                                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                    (Or.inl
                                      (hsame_trans (hsame_symm sameRows) sameO))))))
                              | inr rest =>
                                  cases rest with
                                  | inl sameM =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                        (Or.inr (Or.inl
                                          (hsame_trans (hsame_symm sameRows) sameM)))))))
                                  | inr rest =>
                                      cases rest with
                                      | inl sameG =>
                                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                            (Or.inr (Or.inr (Or.inl
                                              (hsame_trans (hsame_symm sameRows)
                                                sameG))))))))
                                      | inr sameR =>
                                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                                            (Or.inr (Or.inr (Or.inr
                                              (hsame_trans (hsame_symm sameRows)
                                                sameR))))))))
        · exact unary_transport source.right sameRows
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameSource =>
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameSource)))))
      | inr rest =>
          cases rest with
          | inl sameGenerator =>
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl sameGenerator))))))
          | inr rest =>
              cases rest with
              | inl sameMembership =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                    (Or.inr (Or.inl sameMembership)))))))
              | inr rest =>
                  cases rest with
                  | inl sameReadback =>
                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                        (Or.inr (Or.inr sameReadback)))))))
                  | inr rest =>
                      cases rest with
                      | inl sameX => exact Or.inl sameX
                      | inr rest =>
                          cases rest with
                          | inl sameO => exact Or.inr (Or.inl sameO)
                          | inr rest =>
                              cases rest with
                              | inl sameM => exact Or.inr (Or.inr (Or.inl sameM))
                              | inr rest =>
                                  cases rest with
                                  | inl sameG =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inl sameG)))
                                  | inr sameR =>
                                      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameR))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, readbackPkg, provenancePkg⟩
  }
  exact ⟨cert, sourceUnary, generatorUnary, membershipUnary, readbackUnary⟩

end BEDC.Derived.BorelSetUp
