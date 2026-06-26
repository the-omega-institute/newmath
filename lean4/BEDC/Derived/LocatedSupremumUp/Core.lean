import BEDC.Derived.BishopLocatedCauchyRealUp.TasteGate

namespace BEDC.Derived.LocatedSupremumUp

open BEDC.Derived.BishopLocatedCauchyRealUp

abbrev BReal := BishopLocatedCauchyRealUp

def UpperBound (le : BReal -> BReal -> Prop) (S : BReal -> Prop)
    (ub : BReal) : Prop :=
  forall x : BReal, S x -> le x ub

inductive LocatedCutDecision (lt : BReal -> BReal -> Prop)
    (le : BReal -> BReal -> Prop)
    (S : BReal -> Prop) (q r : BReal) : Type where
  | midpoint (x : BReal) (mem : S x) (q_lt_x : lt q x)
      : LocatedCutDecision lt le S q r
  | bound (upper_bound : UpperBound le S r)
      : LocatedCutDecision lt le S q r

def IsLUB (le : BReal -> BReal -> Prop) (S : BReal -> Prop)
    (sup : BReal) : Prop :=
  UpperBound le S sup /\
    forall ub : BReal, UpperBound le S ub -> le sup ub

def LocatedCut (lt : BReal -> BReal -> Prop) (le : BReal -> BReal -> Prop)
    (S : BReal -> Prop) : Type :=
  forall q r : BReal,
    lt q r ->
      LocatedCutDecision lt le S q r

structure LocatedSupData (S : BReal -> Prop) where
  lt : BReal -> BReal -> Prop
  le : BReal -> BReal -> Prop
  witness : BReal
  witness_mem : S witness
  upper : BReal
  upper_bound : UpperBound le S upper
  located_cut : LocatedCut lt le S
  supremum : BReal
  supremum_is_lub : IsLUB le S supremum

def bedcSupLocated {S : BReal -> Prop} (data : LocatedSupData S) : BReal :=
  data.supremum

theorem bedcSupLocated_isLUB {S : BReal -> Prop} (data : LocatedSupData S) :
    IsLUB data.le S (bedcSupLocated data) := by
  exact data.supremum_is_lub

structure LocatedSupremumExportWitness where
  supLocated :
    {S : BReal -> Prop} ->
      LocatedSupData S -> BReal
  isLUB :
    {S : BReal -> Prop} ->
      (data : LocatedSupData S) ->
        IsLUB data.le S (supLocated data)

def locatedSupremumExport : LocatedSupremumExportWitness where
  supLocated := bedcSupLocated
  isLUB := bedcSupLocated_isLUB

def bedcSupLocated_explicit_witness {S : BReal -> Prop}
    (data : LocatedSupData S) : Subtype S :=
  ⟨data.witness, data.witness_mem⟩

def bedcSupLocated_explicit_upper_bound {S : BReal -> Prop}
    (data : LocatedSupData S) :
    Subtype fun ub : BReal => UpperBound data.le S ub :=
  ⟨data.upper, data.upper_bound⟩

def bedcSupLocated_uses_located_cut {S : BReal -> Prop}
    (data : LocatedSupData S) : LocatedCut data.lt data.le S := by
  exact data.located_cut

end BEDC.Derived.LocatedSupremumUp
