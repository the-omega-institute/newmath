import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ArensEellsSpaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ArensEellsSpaceUp : Type where
  | mk :
      (metric basepoint moleculeLedger zeroSum normBudget normedHandoff
        transport replay provenance localName : BHist) →
      ArensEellsSpaceUp
  deriving DecidableEq

def arensEellsSpaceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: arensEellsSpaceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: arensEellsSpaceEncodeBHist h

def arensEellsSpaceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (arensEellsSpaceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (arensEellsSpaceDecodeBHist tail)

private theorem arensEellsSpaceDecode_encode_bhist :
    ∀ h : BHist,
      arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem arensEellsSpace_mk_congr
    {m m' b b' l l' z z' q q' n n' h h' c c' p p' r r' : BHist}
    (hm : m' = m)
    (hb : b' = b)
    (hl : l' = l)
    (hz : z' = z)
    (hq : q' = q)
    (hn : n' = n)
    (hh : h' = h)
    (hc : c' = c)
    (hp : p' = p)
    (hr : r' = r) :
    ArensEellsSpaceUp.mk m' b' l' z' q' n' h' c' p' r' =
      ArensEellsSpaceUp.mk m b l z q n h c p r := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hm
  cases hb
  cases hl
  cases hz
  cases hq
  cases hn
  cases hh
  cases hc
  cases hp
  cases hr
  rfl

def arensEellsSpaceFields : ArensEellsSpaceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ArensEellsSpaceUp.mk m b l z q n h c p r => [m, b, l, z, q, n, h, c, p, r]

def arensEellsSpaceToEventFlow : ArensEellsSpaceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | pkt => (arensEellsSpaceFields pkt).map arensEellsSpaceEncodeBHist

def arensEellsSpaceFromEventFlow : EventFlow → Option ArensEellsSpaceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | m :: rest0 =>
      match rest0 with
      | [] => none
      | b :: rest1 =>
          match rest1 with
          | [] => none
          | l :: rest2 =>
              match rest2 with
              | [] => none
              | z :: rest3 =>
                  match rest3 with
                  | [] => none
                  | q :: rest4 =>
                      match rest4 with
                      | [] => none
                      | n :: rest5 =>
                          match rest5 with
                          | [] => none
                          | h :: rest6 =>
                              match rest6 with
                              | [] => none
                              | c :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | p :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | r :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (ArensEellsSpaceUp.mk
                                                  (arensEellsSpaceDecodeBHist m)
                                                  (arensEellsSpaceDecodeBHist b)
                                                  (arensEellsSpaceDecodeBHist l)
                                                  (arensEellsSpaceDecodeBHist z)
                                                  (arensEellsSpaceDecodeBHist q)
                                                  (arensEellsSpaceDecodeBHist n)
                                                  (arensEellsSpaceDecodeBHist h)
                                                  (arensEellsSpaceDecodeBHist c)
                                                  (arensEellsSpaceDecodeBHist p)
                                                  (arensEellsSpaceDecodeBHist r))
                                          | _ :: _ => none

private theorem arensEellsSpace_round_trip :
    ∀ pkt : ArensEellsSpaceUp,
      arensEellsSpaceFromEventFlow (arensEellsSpaceToEventFlow pkt) = some pkt := by
  -- BEDC touchpoint anchor: BHist BMark
  intro pkt
  cases pkt with
  | mk m b l z q n h c p r =>
      change
        some
          (ArensEellsSpaceUp.mk
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist m))
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist b))
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist l))
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist z))
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist q))
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist n))
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist h))
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist c))
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist p))
            (arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist r))) =
          some (ArensEellsSpaceUp.mk m b l z q n h c p r)
      exact
        congrArg some
          (arensEellsSpace_mk_congr
            (arensEellsSpaceDecode_encode_bhist m)
            (arensEellsSpaceDecode_encode_bhist b)
            (arensEellsSpaceDecode_encode_bhist l)
            (arensEellsSpaceDecode_encode_bhist z)
            (arensEellsSpaceDecode_encode_bhist q)
            (arensEellsSpaceDecode_encode_bhist n)
            (arensEellsSpaceDecode_encode_bhist h)
            (arensEellsSpaceDecode_encode_bhist c)
            (arensEellsSpaceDecode_encode_bhist p)
            (arensEellsSpaceDecode_encode_bhist r))

private theorem arensEellsSpaceToEventFlow_injective {x y : ArensEellsSpaceUp} :
    arensEellsSpaceToEventFlow x = arensEellsSpaceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      arensEellsSpaceFromEventFlow (arensEellsSpaceToEventFlow x) =
        arensEellsSpaceFromEventFlow (arensEellsSpaceToEventFlow y) :=
    congrArg arensEellsSpaceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (arensEellsSpace_round_trip x).symm
      (Eq.trans hread (arensEellsSpace_round_trip y)))

instance arensEellsSpaceBHistCarrier : BHistCarrier ArensEellsSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := arensEellsSpaceToEventFlow
  fromEventFlow := arensEellsSpaceFromEventFlow

instance arensEellsSpaceChapterTasteGate :
    ChapterTasteGate ArensEellsSpaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change arensEellsSpaceFromEventFlow (arensEellsSpaceToEventFlow x) = some x
    exact arensEellsSpace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (arensEellsSpaceToEventFlow_injective heq)

theorem ArensEellsSpaceTasteGate_single_carrier_alignment :
    (∀ h : BHist, arensEellsSpaceDecodeBHist (arensEellsSpaceEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier ArensEellsSpaceUp) ∧
        Nonempty (ChapterTasteGate ArensEellsSpaceUp) ∧
          arensEellsSpaceEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact arensEellsSpaceDecode_encode_bhist
  · constructor
    · exact ⟨arensEellsSpaceBHistCarrier⟩
    · constructor
      · exact ⟨arensEellsSpaceChapterTasteGate⟩
      · rfl

end BEDC.Derived.ArensEellsSpaceUp
