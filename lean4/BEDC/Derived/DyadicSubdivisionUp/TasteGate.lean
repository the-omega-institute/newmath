import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicSubdivisionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicSubdivisionUp : Type where
  | mk (parent level cells mesh validated provenance name : BHist) : DyadicSubdivisionUp
  deriving DecidableEq

def dyadicSubdivisionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicSubdivisionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicSubdivisionEncodeBHist h

def dyadicSubdivisionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicSubdivisionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicSubdivisionDecodeBHist tail)

private theorem dyadicSubdivision_decode_encode :
    ∀ h : BHist,
      dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicSubdivisionFields : DyadicSubdivisionUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | DyadicSubdivisionUp.mk parent level cells mesh validated provenance name =>
      [parent, level, cells, mesh, validated, provenance, name]

def dyadicSubdivisionToEventFlow : DyadicSubdivisionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | DyadicSubdivisionUp.mk parent level cells mesh validated provenance name =>
      [dyadicSubdivisionEncodeBHist parent,
        dyadicSubdivisionEncodeBHist level,
        dyadicSubdivisionEncodeBHist cells,
        dyadicSubdivisionEncodeBHist mesh,
        dyadicSubdivisionEncodeBHist validated,
        dyadicSubdivisionEncodeBHist provenance,
        dyadicSubdivisionEncodeBHist name]

def dyadicSubdivisionFromEventFlow :
    EventFlow → Option DyadicSubdivisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => none
  | _parent :: [] => none
  | _parent :: _level :: [] => none
  | _parent :: _level :: _cells :: [] => none
  | _parent :: _level :: _cells :: _mesh :: [] => none
  | _parent :: _level :: _cells :: _mesh :: _validated :: [] => none
  | _parent :: _level :: _cells :: _mesh :: _validated :: _provenance :: [] => none
  | parent :: level :: cells :: mesh :: validated :: provenance :: name :: [] =>
      some
        (DyadicSubdivisionUp.mk
          (dyadicSubdivisionDecodeBHist parent)
          (dyadicSubdivisionDecodeBHist level)
          (dyadicSubdivisionDecodeBHist cells)
          (dyadicSubdivisionDecodeBHist mesh)
          (dyadicSubdivisionDecodeBHist validated)
          (dyadicSubdivisionDecodeBHist provenance)
          (dyadicSubdivisionDecodeBHist name))
  | _parent :: _level :: _cells :: _mesh :: _validated :: _provenance :: _name ::
      _extra :: _rest => none

private theorem dyadicSubdivision_round_trip :
    ∀ x : DyadicSubdivisionUp,
      dyadicSubdivisionFromEventFlow (dyadicSubdivisionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk parent level cells mesh validated provenance name =>
      exact
        Eq.trans
          (congrArg
            (fun z =>
              some
                (DyadicSubdivisionUp.mk z
                  (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist level))
                  (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist cells))
                  (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist mesh))
                  (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist validated))
                  (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist provenance))
                  (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist name))))
            (dyadicSubdivision_decode_encode parent))
          (Eq.trans
            (congrArg
              (fun z =>
                some
                  (DyadicSubdivisionUp.mk parent z
                    (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist cells))
                    (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist mesh))
                    (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist validated))
                    (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist provenance))
                    (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist name))))
              (dyadicSubdivision_decode_encode level))
            (Eq.trans
              (congrArg
                (fun z =>
                  some
                    (DyadicSubdivisionUp.mk parent level z
                      (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist mesh))
                      (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist validated))
                      (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist provenance))
                      (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist name))))
                (dyadicSubdivision_decode_encode cells))
              (Eq.trans
                (congrArg
                  (fun z =>
                    some
                      (DyadicSubdivisionUp.mk parent level cells z
                        (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist validated))
                        (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist provenance))
                        (dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist name))))
                  (dyadicSubdivision_decode_encode mesh))
                (Eq.trans
                  (congrArg
                    (fun z =>
                      some
                        (DyadicSubdivisionUp.mk parent level cells mesh z
                          (dyadicSubdivisionDecodeBHist
                            (dyadicSubdivisionEncodeBHist provenance))
                          (dyadicSubdivisionDecodeBHist
                            (dyadicSubdivisionEncodeBHist name))))
                    (dyadicSubdivision_decode_encode validated))
                  (Eq.trans
                    (congrArg
                      (fun z =>
                        some
                          (DyadicSubdivisionUp.mk parent level cells mesh validated z
                            (dyadicSubdivisionDecodeBHist
                              (dyadicSubdivisionEncodeBHist name))))
                      (dyadicSubdivision_decode_encode provenance))
                    (congrArg
                      (fun z =>
                        some
                          (DyadicSubdivisionUp.mk parent level cells mesh validated provenance z))
                      (dyadicSubdivision_decode_encode name)))))))

private theorem dyadicSubdivisionEncodeBHist_injective {a b : BHist} :
    dyadicSubdivisionEncodeBHist a = dyadicSubdivisionEncodeBHist b → a = b := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  exact Eq.trans (dyadicSubdivision_decode_encode a).symm
    (Eq.trans (congrArg dyadicSubdivisionDecodeBHist h) (dyadicSubdivision_decode_encode b))

private theorem dyadicSubdivisionToEventFlow_injective
    {x y : DyadicSubdivisionUp} :
    dyadicSubdivisionToEventFlow x = dyadicSubdivisionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hx :
      dyadicSubdivisionFromEventFlow (dyadicSubdivisionToEventFlow x) = some x :=
    dyadicSubdivision_round_trip x
  have hy :
      dyadicSubdivisionFromEventFlow (dyadicSubdivisionToEventFlow y) = some y :=
    dyadicSubdivision_round_trip y
  have hflow :
      dyadicSubdivisionFromEventFlow (dyadicSubdivisionToEventFlow x) =
        dyadicSubdivisionFromEventFlow (dyadicSubdivisionToEventFlow y) :=
    congrArg dyadicSubdivisionFromEventFlow hxy
  have hsome : some x = some y := Eq.trans hx.symm (Eq.trans hflow hy)
  cases hsome
  rfl

private theorem dyadicSubdivision_field_faithful :
    ∀ x y : DyadicSubdivisionUp,
      dyadicSubdivisionFields x = dyadicSubdivisionFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk parent1 level1 cells1 mesh1 validated1 provenance1 name1 =>
      cases y with
      | mk parent2 level2 cells2 mesh2 validated2 provenance2 name2 =>
          cases h
          rfl

instance dyadicSubdivisionBHistCarrier : BHistCarrier DyadicSubdivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicSubdivisionToEventFlow
  fromEventFlow := dyadicSubdivisionFromEventFlow

instance dyadicSubdivisionChapterTasteGate :
    ChapterTasteGate DyadicSubdivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicSubdivisionFromEventFlow (dyadicSubdivisionToEventFlow x) = some x
    exact dyadicSubdivision_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicSubdivisionToEventFlow_injective heq)

instance dyadicSubdivisionFieldFaithful : FieldFaithful DyadicSubdivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicSubdivisionFields
  field_faithful := dyadicSubdivision_field_faithful

instance dyadicSubdivisionNontrivial :
    BEDC.Meta.TasteGate.Nontrivial DyadicSubdivisionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicSubdivisionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      DyadicSubdivisionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicSubdivisionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicSubdivisionChapterTasteGate

theorem DyadicSubdivisionTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicSubdivisionDecodeBHist (dyadicSubdivisionEncodeBHist h) = h) ∧
      (∀ x : DyadicSubdivisionUp,
        dyadicSubdivisionFromEventFlow (dyadicSubdivisionToEventFlow x) = some x) ∧
      (∀ x y : DyadicSubdivisionUp,
        dyadicSubdivisionToEventFlow x = dyadicSubdivisionToEventFlow y → x = y) ∧
      dyadicSubdivisionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨dyadicSubdivision_decode_encode,
      dyadicSubdivision_round_trip,
      fun x y hxy => dyadicSubdivisionToEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.DyadicSubdivisionUp
