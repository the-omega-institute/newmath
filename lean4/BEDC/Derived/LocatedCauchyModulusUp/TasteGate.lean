import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyModulusUp

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

inductive LocatedCauchyModulusUp : Type where
  | mk : (S R D T L E H C P N : BHist) → LocatedCauchyModulusUp
  deriving DecidableEq

def locatedCauchyModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyModulusEncodeBHist h

def locatedCauchyModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyModulusDecodeBHist tail)

private theorem locatedCauchyModulusDecodeEncodeBHist :
    ∀ h : BHist,
      locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedCauchyModulusFields :
    LocatedCauchyModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyModulusUp.mk S R D T L E H C P N =>
      [S, R, D, T, L, E, H, C, P, N]

def locatedCauchyModulusToEventFlow :
    LocatedCauchyModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedCauchyModulusFields x).map locatedCauchyModulusEncodeBHist

def locatedCauchyModulusFromEventFlow :
    EventFlow → Option LocatedCauchyModulusUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | S :: rest0 =>
      match rest0 with
      | [] => none
      | R :: rest1 =>
          match rest1 with
          | [] => none
          | D :: rest2 =>
              match rest2 with
              | [] => none
              | T :: rest3 =>
                  match rest3 with
                  | [] => none
                  | L :: rest4 =>
                      match rest4 with
                      | [] => none
                      | E :: rest5 =>
                          match rest5 with
                          | [] => none
                          | H :: rest6 =>
                              match rest6 with
                              | [] => none
                                  | C :: rest7 =>
                                      match rest7 with
                                      | [] => none
                                      | P :: rest8 =>
                                          match rest8 with
                                          | [] => none
                                          | N :: rest9 =>
                                              match rest9 with
                                              | [] =>
                                                  some
                                                    (LocatedCauchyModulusUp.mk
                                                      (locatedCauchyModulusDecodeBHist S)
                                                      (locatedCauchyModulusDecodeBHist R)
                                                      (locatedCauchyModulusDecodeBHist D)
                                                  (locatedCauchyModulusDecodeBHist T)
                                                  (locatedCauchyModulusDecodeBHist L)
                                                  (locatedCauchyModulusDecodeBHist E)
                                                  (locatedCauchyModulusDecodeBHist H)
                                                  (locatedCauchyModulusDecodeBHist C)
                                                  (locatedCauchyModulusDecodeBHist P)
                                                      (locatedCauchyModulusDecodeBHist N))
                                              | _ :: _ => none

private theorem locatedCauchyModulus_round_trip :
    ∀ x : LocatedCauchyModulusUp,
      locatedCauchyModulusFromEventFlow
        (locatedCauchyModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D T L E H C P N =>
      change
        some
          (LocatedCauchyModulusUp.mk
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist S))
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist R))
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist D))
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist T))
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist L))
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist E))
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist H))
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist C))
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist P))
            (locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist N))) =
          some (LocatedCauchyModulusUp.mk S R D T L E H C P N)
      rw [locatedCauchyModulusDecodeEncodeBHist S,
        locatedCauchyModulusDecodeEncodeBHist R,
        locatedCauchyModulusDecodeEncodeBHist D,
        locatedCauchyModulusDecodeEncodeBHist T,
        locatedCauchyModulusDecodeEncodeBHist L,
        locatedCauchyModulusDecodeEncodeBHist E,
        locatedCauchyModulusDecodeEncodeBHist H,
        locatedCauchyModulusDecodeEncodeBHist C,
        locatedCauchyModulusDecodeEncodeBHist P,
        locatedCauchyModulusDecodeEncodeBHist N]

private theorem locatedCauchyModulusToEventFlow_injective
    {x y : LocatedCauchyModulusUp} :
    locatedCauchyModulusToEventFlow x =
      locatedCauchyModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedCauchyModulusFromEventFlow
          (locatedCauchyModulusToEventFlow x) =
        locatedCauchyModulusFromEventFlow
          (locatedCauchyModulusToEventFlow y) :=
    congrArg locatedCauchyModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedCauchyModulus_round_trip x).symm
      (Eq.trans hread (locatedCauchyModulus_round_trip y)))

private theorem locatedCauchyModulus_fields_faithful :
    ∀ x y : LocatedCauchyModulusUp,
      locatedCauchyModulusFields x = locatedCauchyModulusFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ R₁ D₁ T₁ L₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ R₂ D₂ T₂ L₂ E₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS tailS
          injection tailS with hR tailR
          injection tailR with hD tailD
          injection tailD with hT tailT
          injection tailT with hL tailL
          injection tailL with hE tailE
          injection tailE with hH tailH
          injection tailH with hC tailC
          injection tailC with hP tailP
          injection tailP with hN _
          subst hS
          subst hR
          subst hD
          subst hT
          subst hL
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance locatedCauchyModulusBHistCarrier :
    BHistCarrier LocatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyModulusToEventFlow
  fromEventFlow := locatedCauchyModulusFromEventFlow

instance locatedCauchyModulusChapterTasteGate :
    ChapterTasteGate LocatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCauchyModulusFromEventFlow
      (locatedCauchyModulusToEventFlow x) = some x
    exact locatedCauchyModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCauchyModulusToEventFlow_injective heq)

instance locatedCauchyModulusFieldFaithful :
    FieldFaithful LocatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCauchyModulusFields
  field_faithful := locatedCauchyModulus_fields_faithful

instance locatedCauchyModulusNontrivial :
    Nontrivial LocatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCauchyModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedCauchyModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedCauchyModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCauchyModulusFromEventFlow
      (locatedCauchyModulusToEventFlow x) = some x
    exact locatedCauchyModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCauchyModulusToEventFlow_injective heq)

def LocatedCauchyModulusCarrier [AskSetup] [PackageSetup]
    (S R D T L E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory T ∧
    UnaryHistory L ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg

theorem LocatedCauchyModulusNameCertObligations [AskSetup] [PackageSetup]
    {S R D T L E H C P N windowRead modulusRead sealRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedCauchyModulusCarrier S R D T L E H C P N bundle pkg →
      Cont S R windowRead →
        Cont windowRead D modulusRead →
          Cont T L sealRead →
            Cont H C localRead →
              PkgSig bundle localRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row T ∨
                        hsame row L ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N ∨ hsame row windowRead ∨
                            hsame row modulusRead ∨ hsame row sealRead ∨
                              hsame row localRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont S R windowRead ∧
                        Cont windowRead D modulusRead ∧ Cont T L sealRead ∧
                          Cont H C localRead ∧ PkgSig bundle P pkg ∧
                            PkgSig bundle localRead pkg)
                    hsame ∧
                  UnaryHistory windowRead ∧ UnaryHistory modulusRead ∧
                    UnaryHistory sealRead ∧ UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier sr windowD tl hc pkgLocal
  obtain
    ⟨sUnary, rUnary, dUnary, tUnary, lUnary, _eUnary, hUnary, cUnary, _pUnary,
      _nUnary, carrierPkg⟩ := carrier
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sUnary rUnary sr
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed windowUnary dUnary windowD
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed tUnary lUnary tl
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed hUnary cUnary hc
  have sourceLocal :
      (fun row : BHist => hsame row localRead ∧ UnaryHistory row) localRead := by
    exact ⟨hsame_refl localRead, localUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row T ∨
              hsame row L ∨ hsame row E ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row N ∨ hsame row windowRead ∨
                  hsame row modulusRead ∨ hsame row sealRead ∨ hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R windowRead ∧ Cont windowRead D modulusRead ∧
              Cont T L sealRead ∧ Cont H C localRead ∧ PkgSig bundle P pkg ∧
                PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead sourceLocal
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sr, windowD, tl, hc, carrierPkg, pkgLocal⟩
  }
  exact ⟨cert, windowUnary, modulusUnary, sealUnary, localUnary⟩

theorem LocatedCauchyModulusTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      locatedCauchyModulusDecodeBHist (locatedCauchyModulusEncodeBHist h) = h) ∧
      (∀ x : LocatedCauchyModulusUp,
        locatedCauchyModulusFromEventFlow (locatedCauchyModulusToEventFlow x) = some x) ∧
        (∀ x y : LocatedCauchyModulusUp,
          locatedCauchyModulusToEventFlow x = locatedCauchyModulusToEventFlow y → x = y) ∧
          (∀ x y : LocatedCauchyModulusUp,
            locatedCauchyModulusFields x = locatedCauchyModulusFields y → x = y) ∧
            locatedCauchyModulusEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              locatedCauchyModulusEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
                (∃ x y : LocatedCauchyModulusUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact locatedCauchyModulusDecodeEncodeBHist
  · constructor
    · exact locatedCauchyModulus_round_trip
    · constructor
      · intro x y heq
        exact locatedCauchyModulusToEventFlow_injective heq
      · constructor
        · exact locatedCauchyModulus_fields_faithful
        · constructor
          · rfl
          · constructor
            · rfl
            · exact
                Exists.intro
                  (LocatedCauchyModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
                  (Exists.intro
                    (LocatedCauchyModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
                      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                      BHist.Empty)
                    (by
                      intro h
                      cases h))

end BEDC.Derived.LocatedCauchyModulusUp
