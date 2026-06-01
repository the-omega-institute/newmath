import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.HyperspaceUp

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

inductive HyperspaceUp : Type where
  | mk (X K0 K1 N0 N1 D0 D1 R Hs C P M : BHist) : HyperspaceUp
  deriving DecidableEq

def hyperspaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: hyperspaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: hyperspaceEncodeBHist h

def hyperspaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (hyperspaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (hyperspaceDecodeBHist tail)

private theorem hyperspaceDecode_encode_bhist :
    ∀ h : BHist, hyperspaceDecodeBHist (hyperspaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def hyperspaceFields : HyperspaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | HyperspaceUp.mk X K0 K1 N0 N1 D0 D1 R Hs C P M =>
      [X, K0, K1, N0, N1, D0, D1, R, Hs, C, P, M]

def hyperspaceToEventFlow : HyperspaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (hyperspaceFields x).map hyperspaceEncodeBHist

def hyperspaceFromEventFlow : EventFlow → Option HyperspaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | X :: rest0 =>
      match rest0 with
      | [] => none
      | K0 :: rest1 =>
          match rest1 with
          | [] => none
          | K1 :: rest2 =>
              match rest2 with
              | [] => none
              | N0 :: rest3 =>
                  match rest3 with
                  | [] => none
                  | N1 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | D0 :: rest5 =>
                          match rest5 with
                          | [] => none
                          | D1 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | R :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | Hs :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | C :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | P :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | M :: rest11 =>
                                                  match rest11 with
                                                  | [] =>
                                                      some
                                                        (HyperspaceUp.mk
                                                          (hyperspaceDecodeBHist X)
                                                          (hyperspaceDecodeBHist K0)
                                                          (hyperspaceDecodeBHist K1)
                                                          (hyperspaceDecodeBHist N0)
                                                          (hyperspaceDecodeBHist N1)
                                                          (hyperspaceDecodeBHist D0)
                                                          (hyperspaceDecodeBHist D1)
                                                          (hyperspaceDecodeBHist R)
                                                          (hyperspaceDecodeBHist Hs)
                                                          (hyperspaceDecodeBHist C)
                                                          (hyperspaceDecodeBHist P)
                                                          (hyperspaceDecodeBHist M))
                                                  | _ :: _ => none

private theorem hyperspace_round_trip :
    ∀ x : HyperspaceUp, hyperspaceFromEventFlow (hyperspaceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X K0 K1 N0 N1 D0 D1 R Hs C P M =>
      change
        some
          (HyperspaceUp.mk
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist X))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist K0))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist K1))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist N0))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist N1))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist D0))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist D1))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist R))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist Hs))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist C))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist P))
            (hyperspaceDecodeBHist (hyperspaceEncodeBHist M))) =
          some (HyperspaceUp.mk X K0 K1 N0 N1 D0 D1 R Hs C P M)
      rw [hyperspaceDecode_encode_bhist X, hyperspaceDecode_encode_bhist K0,
        hyperspaceDecode_encode_bhist K1, hyperspaceDecode_encode_bhist N0,
        hyperspaceDecode_encode_bhist N1, hyperspaceDecode_encode_bhist D0,
        hyperspaceDecode_encode_bhist D1, hyperspaceDecode_encode_bhist R,
        hyperspaceDecode_encode_bhist Hs, hyperspaceDecode_encode_bhist C,
        hyperspaceDecode_encode_bhist P, hyperspaceDecode_encode_bhist M]

private theorem hyperspaceToEventFlow_injective {x y : HyperspaceUp} :
    hyperspaceToEventFlow x = hyperspaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      hyperspaceFromEventFlow (hyperspaceToEventFlow x) =
        hyperspaceFromEventFlow (hyperspaceToEventFlow y) :=
    congrArg hyperspaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (hyperspace_round_trip x).symm (Eq.trans hread (hyperspace_round_trip y)))

private theorem hyperspace_fields_faithful :
    ∀ x y : HyperspaceUp, hyperspaceFields x = hyperspaceFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 K01 K11 N01 N11 D01 D11 R1 Hs1 C1 P1 M1 =>
      cases y with
      | mk X2 K02 K12 N02 N12 D02 D12 R2 Hs2 C2 P2 M2 =>
          cases hfields
          rfl

instance hyperspaceBHistCarrier : BHistCarrier HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := hyperspaceToEventFlow
  fromEventFlow := hyperspaceFromEventFlow

instance hyperspaceChapterTasteGate : ChapterTasteGate HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change hyperspaceFromEventFlow (hyperspaceToEventFlow x) = some x
    exact hyperspace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (hyperspaceToEventFlow_injective heq)

instance hyperspaceFieldFaithful : FieldFaithful HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := hyperspaceFields
  field_faithful := hyperspace_fields_faithful

instance hyperspaceNontrivial : Nontrivial HyperspaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨HyperspaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      HyperspaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem HyperspaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate HyperspaceUp) ∧ Nonempty (FieldFaithful HyperspaceUp) ∧
      Nonempty (Nontrivial HyperspaceUp) ∧
        (∀ h : BHist, hyperspaceDecodeBHist (hyperspaceEncodeBHist h) = h) ∧
          (∀ x : HyperspaceUp,
            hyperspaceFromEventFlow (hyperspaceToEventFlow x) = some x) ∧
            hyperspaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · exact ⟨hyperspaceChapterTasteGate⟩
  · constructor
    · exact ⟨hyperspaceFieldFaithful⟩
    · constructor
      · exact ⟨hyperspaceNontrivial⟩
      · constructor
        · exact hyperspaceDecode_encode_bhist
        · constructor
          · exact hyperspace_round_trip
          · rfl

def HyperspaceCarrier [AskSetup] [PackageSetup]
    (X K0 K1 N0 N1 D0 D1 R Hs C P M : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory X ∧ UnaryHistory K0 ∧ UnaryHistory K1 ∧ UnaryHistory N0 ∧
    UnaryHistory N1 ∧ UnaryHistory D0 ∧ UnaryHistory D1 ∧ UnaryHistory R ∧
      UnaryHistory Hs ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory M ∧
        PkgSig bundle P pkg

theorem Hyperspace_hausdorff_distance_stability [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M distanceRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont D0 D1 distanceRead →
        Cont distanceRead R publicRead →
          PkgSig bundle publicRead pkg →
            UnaryHistory distanceRead ∧ UnaryHistory publicRead ∧
              hsame distanceRead (append D0 D1) ∧
                SemanticNameCert
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row X ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                      hsame row distanceRead ∨ hsame row publicRead)
                  (fun row : BHist =>
                    hsame row publicRead ∧ PkgSig bundle P pkg ∧
                      PkgSig bundle publicRead pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier distanceRoute publicRoute publicPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, pUnary, _mUnary, provenancePkg⟩ := carrier
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed d0Unary d1Unary distanceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed distanceUnary rUnary publicRoute
  have distanceExact : hsame distanceRead (append D0 D1) := distanceRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
            hsame row distanceRead ∨ hsame row publicRead)
        (fun row : BHist =>
          hsame row publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead (And.intro (hsame_refl publicRead) publicUnary)
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
        intro row row' sameRows source
        have samePublic : hsame row' publicRead :=
          hsame_trans (hsame_symm sameRows) source.left
        have rowUnary : UnaryHistory row' :=
          unary_transport source.right sameRows
        exact And.intro samePublic rowUnary
    }
    pattern_sound := by
      intro row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro row source
      exact And.intro source.left (And.intro provenancePkg publicPkg)
  }
  exact ⟨distanceUnary, publicUnary, distanceExact, cert⟩

theorem Hyperspace_hausdorff_distance_window [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M distanceRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont D0 D1 distanceRead →
        Cont distanceRead R publicRead →
          PkgSig bundle publicRead pkg →
            UnaryHistory D0 ∧ UnaryHistory D1 ∧ UnaryHistory R ∧
              UnaryHistory distanceRead ∧ UnaryHistory publicRead ∧
                hsame distanceRead (append D0 D1) ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier distanceRoute publicRoute publicPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed d0Unary d1Unary distanceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed distanceUnary rUnary publicRoute
  exact
    ⟨d0Unary, d1Unary, rUnary, distanceUnary, publicUnary, distanceRoute,
      provenancePkg, publicPkg⟩

theorem Hyperspace_compactmetric_distance_lift [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M subsetRead netRead distanceRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 K1 subsetRead →
        Cont N0 N1 netRead →
          Cont D0 D1 distanceRead →
            Cont distanceRead R publicRead →
              PkgSig bundle publicRead pkg →
                UnaryHistory subsetRead ∧ UnaryHistory netRead ∧
                  UnaryHistory distanceRead ∧ UnaryHistory publicRead ∧
                    SemanticNameCert
                      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
                          hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
                            hsame row subsetRead ∨ hsame row netRead ∨
                              hsame row distanceRead ∨ hsame row publicRead)
                      (fun row : BHist =>
                        hsame row publicRead ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle publicRead pkg)
                      hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro carrier subsetRoute netRoute distanceRoute publicRoute publicPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have subsetUnary : UnaryHistory subsetRead :=
    unary_cont_closed k0Unary k1Unary subsetRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed n0Unary n1Unary netRoute
  have distanceUnary : UnaryHistory distanceRead :=
    unary_cont_closed d0Unary d1Unary distanceRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed distanceUnary rUnary publicRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row X ∨ hsame row K0 ∨ hsame row K1 ∨ hsame row N0 ∨
            hsame row N1 ∨ hsame row D0 ∨ hsame row D1 ∨ hsame row R ∨
              hsame row subsetRead ∨ hsame row netRead ∨ hsame row distanceRead ∨
                hsame row publicRead)
        (fun row : BHist =>
          hsame row publicRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, publicPkg⟩
  }
  exact ⟨subsetUnary, netUnary, distanceUnary, publicUnary, cert⟩

theorem Hyperspace_directed_hausdorff_root_coverage [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M directedLeft directedRight symmetricRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont D0 R directedLeft →
        Cont D1 R directedRight →
          Cont directedLeft directedRight symmetricRead →
            PkgSig bundle symmetricRead pkg →
              UnaryHistory D0 ∧ UnaryHistory D1 ∧ UnaryHistory R ∧
                UnaryHistory directedLeft ∧ UnaryHistory directedRight ∧
                  UnaryHistory symmetricRead ∧ Cont D0 R directedLeft ∧
                    Cont D1 R directedRight ∧ Cont directedLeft directedRight symmetricRead ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle symmetricRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory
  intro carrier directedLeftRoute directedRightRoute symmetricRoute symmetricPkg
  obtain ⟨_xUnary, _k0Unary, _k1Unary, _n0Unary, _n1Unary, d0Unary, d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have directedLeftUnary : UnaryHistory directedLeft :=
    unary_cont_closed d0Unary rUnary directedLeftRoute
  have directedRightUnary : UnaryHistory directedRight :=
    unary_cont_closed d1Unary rUnary directedRightRoute
  have symmetricUnary : UnaryHistory symmetricRead :=
    unary_cont_closed directedLeftUnary directedRightUnary symmetricRoute
  exact
    ⟨d0Unary, d1Unary, rUnary, directedLeftUnary, directedRightUnary, symmetricUnary,
      directedLeftRoute, directedRightRoute, symmetricRoute, provenancePkg, symmetricPkg⟩

theorem Hyperspace_totallybounded_net_lift [AskSetup] [PackageSetup]
    {X K0 K1 N0 N1 D0 D1 R Hs C P M netLeft netRight directedRead publicRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    HyperspaceCarrier X K0 K1 N0 N1 D0 D1 R Hs C P M bundle pkg →
      Cont K0 N0 netLeft →
        Cont K1 N1 netRight →
          Cont netLeft netRight directedRead →
            Cont directedRead R publicRead →
              PkgSig bundle publicRead pkg →
                UnaryHistory netLeft ∧ UnaryHistory netRight ∧
                  UnaryHistory directedRead ∧ UnaryHistory publicRead ∧
                    hsame directedRead (append netLeft netRight) ∧
                      PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame UnaryHistory
  intro carrier netLeftRoute netRightRoute directedRoute publicRoute publicPkg
  obtain ⟨_xUnary, k0Unary, k1Unary, n0Unary, n1Unary, _d0Unary, _d1Unary,
    rUnary, _hsUnary, _cUnary, _pUnary, _mUnary, provenancePkg⟩ := carrier
  have netLeftUnary : UnaryHistory netLeft :=
    unary_cont_closed k0Unary n0Unary netLeftRoute
  have netRightUnary : UnaryHistory netRight :=
    unary_cont_closed k1Unary n1Unary netRightRoute
  have directedUnary : UnaryHistory directedRead :=
    unary_cont_closed netLeftUnary netRightUnary directedRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed directedUnary rUnary publicRoute
  exact
    ⟨netLeftUnary, netRightUnary, directedUnary, publicUnary, directedRoute,
      provenancePkg, publicPkg⟩

end BEDC.Derived.HyperspaceUp
