import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteWitnessRouteUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteWitnessRouteUp : Type where
  | mk : (q w r d s h c p n : BHist) → FiniteWitnessRouteUp
  deriving DecidableEq

def finiteWitnessRouteEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteWitnessRouteEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteWitnessRouteEncodeBHist h

def finiteWitnessRouteDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteWitnessRouteDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteWitnessRouteDecodeBHist tail)

theorem FiniteWitnessRouteTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteWitnessRouteToEventFlow : FiniteWitnessRouteUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteWitnessRouteUp.mk q w r d s h c p n =>
      [[BMark.b0],
        finiteWitnessRouteEncodeBHist q,
        [BMark.b1, BMark.b0],
        finiteWitnessRouteEncodeBHist w,
        [BMark.b1, BMark.b1, BMark.b0],
        finiteWitnessRouteEncodeBHist r,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWitnessRouteEncodeBHist d,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWitnessRouteEncodeBHist s,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWitnessRouteEncodeBHist h,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        finiteWitnessRouteEncodeBHist c,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        finiteWitnessRouteEncodeBHist p,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        finiteWitnessRouteEncodeBHist n]

def finiteWitnessRouteFromEventFlow : EventFlow → Option FiniteWitnessRouteUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | q :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | w :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | r :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | d :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | s :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | h :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | c :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | p :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | n :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (FiniteWitnessRouteUp.mk
                                                                                  (finiteWitnessRouteDecodeBHist q)
                                                                                  (finiteWitnessRouteDecodeBHist w)
                                                                                  (finiteWitnessRouteDecodeBHist r)
                                                                                  (finiteWitnessRouteDecodeBHist d)
                                                                                  (finiteWitnessRouteDecodeBHist s)
                                                                                  (finiteWitnessRouteDecodeBHist h)
                                                                                  (finiteWitnessRouteDecodeBHist c)
                                                                                  (finiteWitnessRouteDecodeBHist p)
                                                                                  (finiteWitnessRouteDecodeBHist n))
                                                                          | _ :: _ => none

theorem FiniteWitnessRouteTasteGate_single_carrier_alignment_round_trip :
    ∀ x : FiniteWitnessRouteUp,
      finiteWitnessRouteFromEventFlow (finiteWitnessRouteToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q w r d s h c p n =>
      change
        some
          (FiniteWitnessRouteUp.mk
            (finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist q))
            (finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist w))
            (finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist r))
            (finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist d))
            (finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist s))
            (finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist h))
            (finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist c))
            (finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist p))
            (finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist n))) =
          some (FiniteWitnessRouteUp.mk q w r d s h c p n)
      rw [FiniteWitnessRouteTasteGate_single_carrier_alignment_decode q,
        FiniteWitnessRouteTasteGate_single_carrier_alignment_decode w,
        FiniteWitnessRouteTasteGate_single_carrier_alignment_decode r,
        FiniteWitnessRouteTasteGate_single_carrier_alignment_decode d,
        FiniteWitnessRouteTasteGate_single_carrier_alignment_decode s,
        FiniteWitnessRouteTasteGate_single_carrier_alignment_decode h,
        FiniteWitnessRouteTasteGate_single_carrier_alignment_decode c,
        FiniteWitnessRouteTasteGate_single_carrier_alignment_decode p,
        FiniteWitnessRouteTasteGate_single_carrier_alignment_decode n]

theorem FiniteWitnessRouteTasteGate_single_carrier_alignment_injective
    {x y : FiniteWitnessRouteUp} :
    finiteWitnessRouteToEventFlow x = finiteWitnessRouteToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteWitnessRouteFromEventFlow (finiteWitnessRouteToEventFlow x) =
        finiteWitnessRouteFromEventFlow (finiteWitnessRouteToEventFlow y) :=
    congrArg finiteWitnessRouteFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (FiniteWitnessRouteTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (FiniteWitnessRouteTasteGate_single_carrier_alignment_round_trip y)))

instance finiteWitnessRouteBHistCarrier : BHistCarrier FiniteWitnessRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteWitnessRouteToEventFlow
  fromEventFlow := finiteWitnessRouteFromEventFlow

instance finiteWitnessRouteChapterTasteGate : ChapterTasteGate FiniteWitnessRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change finiteWitnessRouteFromEventFlow (finiteWitnessRouteToEventFlow x) = some x
    exact FiniteWitnessRouteTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (FiniteWitnessRouteTasteGate_single_carrier_alignment_injective heq)

instance finiteWitnessRouteFieldFaithful : FieldFaithful FiniteWitnessRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | FiniteWitnessRouteUp.mk q w r d s h c p n => [q, w, r, d, s, h, c, p, n]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk q1 w1 r1 d1 s1 h1 c1 p1 n1 =>
        cases y with
        | mk q2 w2 r2 d2 s2 h2 c2 p2 n2 =>
            injection hfields with hq tail1
            cases hq
            injection tail1 with hw tail2
            cases hw
            injection tail2 with hr tail3
            cases hr
            injection tail3 with hd tail4
            cases hd
            injection tail4 with hs tail5
            cases hs
            injection tail5 with hh tail6
            cases hh
            injection tail6 with hc tail7
            cases hc
            injection tail7 with hp tail8
            cases hp
            injection tail8 with hn _
            cases hn
            rfl

instance finiteWitnessRouteNontrivial : Nontrivial FiniteWitnessRouteUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteWitnessRouteUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteWitnessRouteUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hq
        cases hq⟩

theorem FiniteWitnessRouteTasteGate_single_carrier_alignment :
    (∀ h : BHist, finiteWitnessRouteDecodeBHist (finiteWitnessRouteEncodeBHist h) = h) ∧
      (∀ x : FiniteWitnessRouteUp,
        finiteWitnessRouteFromEventFlow (finiteWitnessRouteToEventFlow x) = some x) ∧
        (∀ x y : FiniteWitnessRouteUp,
          finiteWitnessRouteToEventFlow x = finiteWitnessRouteToEventFlow y → x = y) ∧
          finiteWitnessRouteEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact FiniteWitnessRouteTasteGate_single_carrier_alignment_decode
  · constructor
    · exact FiniteWitnessRouteTasteGate_single_carrier_alignment_round_trip
    · constructor
      · intro x y heq
        exact FiniteWitnessRouteTasteGate_single_carrier_alignment_injective heq
      · rfl

theorem FiniteWitnessRouteNameCert_obligations
    {q w r d s h c p n : BHist}
    (requestRoute : Cont q w r)
    (sealRoute : Cont r d s) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row q ∧
          ∃ packet : FiniteWitnessRouteUp,
            packet = FiniteWitnessRouteUp.mk q w r d s h c p n)
      (fun row : BHist => hsame row q ∧ hsame w w ∧ hsame r r ∧ hsame d d)
      (fun row : BHist =>
        Cont q w r ∧ Cont r d s ∧ hsame row q ∧ hsame h h ∧ hsame c c ∧
          hsame p p ∧ hsame n n)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro q
          ⟨hsame_refl q, Exists.intro (FiniteWitnessRouteUp.mk q w r d s h c p n) rfl⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left, sourceRow.right⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, hsame_refl w, hsame_refl r, hsame_refl d⟩
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨requestRoute, sealRoute, sourceRow.left, hsame_refl h, hsame_refl c,
          hsame_refl p, hsame_refl n⟩
  }

end BEDC.Derived.FiniteWitnessRouteUp
