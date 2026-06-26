import BEDC.Algebra.FiniteFold
import BEDC.Algebra.Rel.IntegerUp
import BEDC.Algebra.Rel.InterfaceSpine
import BEDC.Algebra.Spine.Arithmetic
import BEDC.Derived.MatrixUp.FiniteFold

namespace BEDC.Algebra.Spine.GeometryCategoryHomology

open BEDC.Algebra.FiniteFold
open BEDC.Algebra.Rel
open BEDC.Algebra.Spine.Arithmetic
open BEDC.Algebra.Spine.FiniteData
open BEDC.Derived.MatrixUp
open BEDC.FKernel.Hist

abbrev Hist := BHist

structure CategoryUp where
  Obj : CarrierUp
  Hom : Hist -> Hist -> CarrierUp
  hom_obj_congr :
    forall {x x' y y' : Hist},
      Obj.same x x' -> Obj.same y y' ->
        forall {f g : Hist}, (Hom x y).same f g -> (Hom x' y').same f g
  id : forall x : Hist, Obj.carrier x -> Hist
  id_carrier : forall {x : Hist} (hx : Obj.carrier x), (Hom x x).carrier (id x hx)
  comp : Hist -> Hist -> Hist
  comp_carrier :
    forall {x y z : Hist} {f g : Hist},
      (Hom x y).carrier f -> (Hom y z).carrier g ->
        (Hom x z).carrier (comp g f)
  comp_congr :
    forall {x y z : Hist} {f f' g g' : Hist},
      (Hom x y).same f f' -> (Hom y z).same g g' ->
        (Hom x z).same
          (comp g f)
          (comp g' f')
  id_left :
    forall {x y : Hist} (_hx : Obj.carrier x) (hy : Obj.carrier y) {f : Hist},
      (Hom x y).carrier f ->
        (Hom x y).same (comp (id y hy) f) f
  id_right :
    forall {x y : Hist} (hx : Obj.carrier x) (_hy : Obj.carrier y) {f : Hist},
      (Hom x y).carrier f ->
        (Hom x y).same (comp f (id x hx)) f
  assoc :
    forall {w x y z : Hist} {f g h : Hist},
      (Hom w x).carrier f -> (Hom x y).carrier g -> (Hom y z).carrier h ->
        (Hom w z).same
          (comp h (comp g f))
          (comp (comp h g) f)

namespace CategoryUp

theorem id_left_checked (C : CategoryUp)
    {x y : Hist} (hx : C.Obj.carrier x) (hy : C.Obj.carrier y) {f : Hist}
    (hf : (C.Hom x y).carrier f) :
    (C.Hom x y).same (C.comp (C.id y hy) f) f :=
  C.id_left hx hy hf

theorem id_right_checked (C : CategoryUp)
    {x y : Hist} (hx : C.Obj.carrier x) (hy : C.Obj.carrier y) {f : Hist}
    (hf : (C.Hom x y).carrier f) :
    (C.Hom x y).same (C.comp f (C.id x hx)) f :=
  C.id_right hx hy hf

theorem assoc_checked (C : CategoryUp)
    {w x y z : Hist} {f g h : Hist}
    (hf : (C.Hom w x).carrier f) (hg : (C.Hom x y).carrier g)
    (hh : (C.Hom y z).carrier h) :
    (C.Hom w z).same
      (C.comp h (C.comp g f))
      (C.comp (C.comp h g) f) :=
  C.assoc hf hg hh

end CategoryUp

structure FunctorUp (C D : CategoryUp) where
  objMap : Hist -> Hist
  obj_carrier : forall {x : Hist}, C.Obj.carrier x -> D.Obj.carrier (objMap x)
  obj_congr : forall {x y : Hist}, C.Obj.same x y -> D.Obj.same (objMap x) (objMap y)
  homMap : Hist -> Hist -> Hist -> Hist
  hom_carrier :
    forall {x y : Hist} {f : Hist},
      (C.Hom x y).carrier f -> (D.Hom (objMap x) (objMap y)).carrier (homMap x y f)
  hom_congr :
    forall {x y : Hist} {f g : Hist},
      (C.Hom x y).same f g ->
        (D.Hom (objMap x) (objMap y)).same (homMap x y f) (homMap x y g)
  map_id :
    forall {x : Hist} (hx : C.Obj.carrier x),
      (D.Hom (objMap x) (objMap x)).same
        (homMap x x (C.id x hx))
        (D.id (objMap x) (obj_carrier hx))
  map_comp :
    forall {x y z : Hist} {f g : Hist},
      (C.Hom x y).carrier f -> (C.Hom y z).carrier g ->
        (D.Hom (objMap x) (objMap z)).same
          (homMap x z (C.comp g f))
          (D.comp (homMap y z g) (homMap x y f))

namespace FunctorUp

def identity (C : CategoryUp) : FunctorUp C C where
  objMap := fun x => x
  obj_carrier := by
    intro x hx
    exact hx
  obj_congr := by
    intro x y hxy
    exact hxy
  homMap := fun _x _y f => f
  hom_carrier := by
    intro x y f hf
    exact hf
  hom_congr := by
    intro x y f g hfg
    exact hfg
  map_id := by
    intro x hx
    exact (C.Hom x x).same_refl (C.id_carrier hx)
  map_comp := by
    intro x y z f g hf hg
    exact (C.Hom x z).same_refl (C.comp_carrier hf hg)

def comp {C D E : CategoryUp} (G : FunctorUp D E) (F : FunctorUp C D) :
    FunctorUp C E where
  objMap := fun x => G.objMap (F.objMap x)
  obj_carrier := by
    intro x hx
    exact G.obj_carrier (F.obj_carrier hx)
  obj_congr := by
    intro x y hxy
    exact G.obj_congr (F.obj_congr hxy)
  homMap := fun x y f => G.homMap (F.objMap x) (F.objMap y) (F.homMap x y f)
  hom_carrier := by
    intro x y f hf
    exact G.hom_carrier (F.hom_carrier hf)
  hom_congr := by
    intro x y f g hfg
    exact G.hom_congr (F.hom_congr hfg)
  map_id := by
    intro x hx
    exact (E.Hom (G.objMap (F.objMap x)) (G.objMap (F.objMap x))).same_trans
      (G.hom_carrier (F.hom_carrier (C.id_carrier hx)))
      (G.hom_carrier (D.id_carrier (F.obj_carrier hx)))
      (E.id_carrier (G.obj_carrier (F.obj_carrier hx)))
      (G.hom_congr (F.map_id hx))
      (G.map_id (F.obj_carrier hx))
  map_comp := by
    intro x y z f g hf hg
    exact (E.Hom (G.objMap (F.objMap x)) (G.objMap (F.objMap z))).same_trans
      (G.hom_carrier (F.hom_carrier (C.comp_carrier hf hg)))
      (G.hom_carrier
        (D.comp_carrier (F.hom_carrier hf) (F.hom_carrier hg)))
      (E.comp_carrier (G.hom_carrier (F.hom_carrier hf))
        (G.hom_carrier (F.hom_carrier hg)))
      (G.hom_congr (F.map_comp hf hg))
      (G.map_comp (F.hom_carrier hf) (F.hom_carrier hg))

theorem comp_preserves_id {C D E : CategoryUp}
    (G : FunctorUp D E) (F : FunctorUp C D)
    {x : Hist} (hx : C.Obj.carrier x) :
    (E.Hom ((comp G F).objMap x) ((comp G F).objMap x)).same
      ((comp G F).homMap x x (C.id x hx))
      (E.id ((comp G F).objMap x) ((comp G F).obj_carrier hx)) :=
  (comp G F).map_id hx

end FunctorUp

def UnitHistCarrier (h : Hist) : Prop :=
  hsame h emp

def UnitHistSame (h k : Hist) : Prop :=
  UnitHistCarrier h /\ UnitHistCarrier k /\ hsame h k

theorem unit_hist_carrier_emp : UnitHistCarrier emp :=
  hsame_refl emp

def unit_hist_same_equiv : RelEquiv { h : Hist // UnitHistCarrier h } where
  rel x y := UnitHistSame x.1 y.1
  refl := by
    intro x
    exact ⟨x.2, x.2, hsame_refl x.1⟩
  symm := by
    intro x y sameXY
    exact ⟨sameXY.right.left, sameXY.left, hsame_symm sameXY.right.right⟩
  trans := by
    intro x y z sameXY sameYZ
    exact ⟨sameXY.left, sameYZ.right.left,
      hsame_trans sameXY.right.right sameYZ.right.right⟩

def UnitHistCarrierUp : CarrierUp where
  carrier := UnitHistCarrier
  same := UnitHistSame
  same_equiv := unit_hist_same_equiv
  same_left_carrier := by
    intro h k sameHK
    exact sameHK.left
  same_right_carrier := by
    intro h k sameHK
    exact sameHK.right.left
  same_equiv_sound := by
    intro h k _hh _hk sameHK
    exact sameHK
  same_equiv_complete := by
    intro h k _hh _hk sameHK
    exact sameHK

def BoolHomUp (_x _y : Hist) : CarrierUp :=
  UnitHistCarrierUp

def BoolCategoryUp : CategoryUp where
  Obj := BoolCarrierUp
  Hom := BoolHomUp
  hom_obj_congr := by
    intro x x' y y' _sameX _sameY f g sameFG
    exact sameFG
  id := fun _x _hx => emp
  id_carrier := by
    intro x hx
    exact unit_hist_carrier_emp
  comp := fun _g _f => emp
  comp_carrier := by
    intro x y z f g hf hg
    exact unit_hist_carrier_emp
  comp_congr := by
    intro x y z f f' g g' sameF sameG
    exact UnitHistCarrierUp.same_refl unit_hist_carrier_emp
  id_left := by
    intro x y hx hy f hf
    exact ⟨unit_hist_carrier_emp, hf, hsame_symm hf⟩
  id_right := by
    intro x y hx hy f hf
    exact ⟨unit_hist_carrier_emp, hf, hsame_symm hf⟩
  assoc := by
    intro w x y z f g h hf hg hh
    exact UnitHistCarrierUp.same_refl unit_hist_carrier_emp

def BoolCategoryIdentityFunctor : FunctorUp BoolCategoryUp BoolCategoryUp :=
  FunctorUp.identity BoolCategoryUp

theorem boolCategory_id_left {x y f : Hist}
    (hx : BoolCategoryUp.Obj.carrier x) (hy : BoolCategoryUp.Obj.carrier y)
    (hf : (BoolCategoryUp.Hom x y).carrier f) :
    (BoolCategoryUp.Hom x y).same
      (BoolCategoryUp.comp (BoolCategoryUp.id y hy) f) f :=
  BoolCategoryUp.id_left hx hy hf

structure FiniteModuleUp
    (RCarrier : Type u) (RE : RelEquiv RCarrier) (R : RingUp RCarrier RE) where
  MCarrier : Type v
  ME : RelEquiv MCarrier
  addGroup : AbGroupUp MCarrier ME
  module : ModuleUp RCarrier RE MCarrier ME R addGroup
  basisLabels : List Hist
  coordinates : MCarrier -> List RCarrier
  coordinates_congr :
    forall {x y : MCarrier}, ME.rel x y ->
      ListPairwiseRel RE.rel (coordinates x) (coordinates y)

structure LinearMapUp
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    (M N : FiniteModuleUp RCarrier RE R) where
  toFun : M.MCarrier -> N.MCarrier
  map_congr : forall {x y : M.MCarrier}, M.ME.rel x y -> N.ME.rel (toFun x) (toFun y)
  map_zero : forall x : M.MCarrier, M.ME.rel x M.addGroup.one -> N.ME.rel (toFun x) N.addGroup.one
  map_add :
    forall x y : M.MCarrier,
      N.ME.rel (toFun (M.addGroup.op x y)) (N.addGroup.op (toFun x) (toFun y))
  map_smul :
    forall (a : RCarrier) (x : M.MCarrier),
      N.ME.rel (toFun (M.module.smul a x)) (N.module.smul a (toFun x))

def LinearMapUp.comp
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    {L M N : FiniteModuleUp RCarrier RE R}
    (g : LinearMapUp M N) (f : LinearMapUp L M) : LinearMapUp L N where
  toFun := fun x => g.toFun (f.toFun x)
  map_congr := by
    intro x y hxy
    exact g.map_congr (f.map_congr hxy)
  map_zero := by
    intro x hx
    exact g.map_zero (f.toFun x) (f.map_zero x hx)
  map_add := by
    intro x y
    exact N.ME.trans
      (g.map_congr (f.map_add x y))
      (g.map_add (f.toFun x) (f.toFun y))
  map_smul := by
    intro a x
    exact N.ME.trans
      (g.map_congr (f.map_smul a x))
      (g.map_smul a (f.toFun x))

structure BoundarySquareZeroUp
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    {L M N : FiniteModuleUp RCarrier RE R}
    (left : LinearMapUp L M) (right : LinearMapUp M N) where
  square_zero : forall x : L.MCarrier, N.ME.rel (right.toFun (left.toFun x)) N.addGroup.one

structure ChainTermUp
    (RCarrier : Type u) (RE : RelEquiv RCarrier) (R : RingUp RCarrier RE) where
  degree : Hist
  degree_carrier : NatCarrierUp.carrier degree
  module : FiniteModuleUp RCarrier RE R

structure ChainBoundaryUp
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    (source target : ChainTermUp RCarrier RE R) where
  boundary : LinearMapUp source.module target.module

structure ChainSquareRowUp
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    {L M N : ChainTermUp RCarrier RE R}
    (first : ChainBoundaryUp L M) (second : ChainBoundaryUp M N) where
  row_zero : BoundarySquareZeroUp first.boundary second.boundary

structure ChainSquareEntryUp
    (RCarrier : Type u) (RE : RelEquiv RCarrier) (R : RingUp RCarrier RE) where
  L : ChainTermUp RCarrier RE R
  M : ChainTermUp RCarrier RE R
  N : ChainTermUp RCarrier RE R
  first : ChainBoundaryUp L M
  second : ChainBoundaryUp M N
  row : ChainSquareRowUp first second

structure ChainComplexUp
    (RCarrier : Type u) (RE : RelEquiv RCarrier) (R : RingUp RCarrier RE) where
  terms : List (ChainTermUp RCarrier RE R)
  boundaries :
    List (Sigma fun source : ChainTermUp RCarrier RE R =>
      Sigma fun target : ChainTermUp RCarrier RE R =>
        ChainBoundaryUp source target)
  squareRows : List (ChainSquareEntryUp RCarrier RE R)
  finite_degrees : List Hist := terms.map (fun term => term.degree)

theorem chain_square_zero
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    {L M N : ChainTermUp RCarrier RE R}
    {first : ChainBoundaryUp L M} {second : ChainBoundaryUp M N}
    (row : ChainSquareRowUp first second) (x : L.module.MCarrier) :
    N.module.ME.rel
      (second.boundary.toFun (first.boundary.toFun x))
      N.module.addGroup.one :=
  row.row_zero.square_zero x

def HomologyBoundaryDifference
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    {M : FiniteModuleUp RCarrier RE R}
    (boundary : M.MCarrier -> Prop)
    (x y : M.MCarrier) : Prop :=
  boundary (M.addGroup.op x (M.addGroup.inv y))

structure HomologyReadout
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    (M : FiniteModuleUp RCarrier RE R) where
  degree : Hist
  degree_carrier : NatCarrierUp.carrier degree
  cycle : M.MCarrier -> Prop
  boundary : M.MCarrier -> Prop
  cycle_congr : forall {x y : M.MCarrier}, M.ME.rel x y -> cycle x -> cycle y
  boundary_congr : forall {x y : M.MCarrier}, M.ME.rel x y -> boundary x -> boundary y
  boundary_cycle : forall {x : M.MCarrier}, boundary x -> cycle x
  homologous : {x : M.MCarrier // cycle x} -> {y : M.MCarrier // cycle y} -> Prop
  homologous_equiv : RelEquiv {x : M.MCarrier // cycle x}
  homologous_sound :
    forall x y : {x : M.MCarrier // cycle x},
      homologous_equiv.rel x y -> homologous x y
  homologous_complete :
    forall x y : {x : M.MCarrier // cycle x},
      homologous x y -> homologous_equiv.rel x y
  homologous_boundary_sound :
    forall x y : {x : M.MCarrier // cycle x},
      homologous x y -> HomologyBoundaryDifference boundary x.1 y.1
  homologous_boundary_complete :
    forall x y : {x : M.MCarrier // cycle x},
      HomologyBoundaryDifference boundary x.1 y.1 -> homologous x y
  finite_representatives : List M.MCarrier

def HomologyReadout.relEquiv
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    {M : FiniteModuleUp RCarrier RE R} (H : HomologyReadout M) :
    RelEquiv {x : M.MCarrier // H.cycle x} :=
  H.homologous_equiv

theorem homology_boundary_is_cycle
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    {M : FiniteModuleUp RCarrier RE R} (H : HomologyReadout M)
    {x : M.MCarrier} :
    H.boundary x -> H.cycle x :=
  H.boundary_cycle

theorem homology_rel_is_boundary_difference
    {RCarrier : Type u} {RE : RelEquiv RCarrier} {R : RingUp RCarrier RE}
    {M : FiniteModuleUp RCarrier RE R} (H : HomologyReadout M)
    (x y : {x : M.MCarrier // H.cycle x}) :
    H.homologous x y -> HomologyBoundaryDifference H.boundary x.1 y.1 :=
  H.homologous_boundary_sound x y

structure SimplexUp where
  vertices : List Hist
  dimension : Hist
  dimension_carrier : NatCarrierUp.carrier dimension

structure IncidenceEntryUp where
  source : SimplexUp
  target : SimplexUp
  coefficient : BEDC.Algebra.Rel.IntegerUp

structure IncidenceMatrixUp where
  rows : List (List BEDC.Algebra.Rel.IntegerUp)
  matrixCode : Hist
  matrixCode_carrier : MatrixSingletonCarrier matrixCode

structure SimplicialComplexUp where
  simplices : List SimplexUp
  incidence : IncidenceMatrixUp
  faceRows : List IncidenceEntryUp
  simplexCountByDegree : List BEDC.Algebra.Rel.IntegerUp

def alternatingSum {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) : List A -> A
  | [] => R.zero
  | x :: xs => R.add x (R.neg (alternatingSum R xs))

theorem alternatingSum_congr {A : Type u} {r : A -> A -> Prop}
    (R : RelCommRing A r) {xs ys : List A} :
    ListPairwiseRel r xs ys ->
      r (alternatingSum R xs) (alternatingSum R ys) := by
  intro paired
  induction paired with
  | nil =>
      exact R.refl R.zero
  | cons head tail ih =>
      exact R.add_congr head (R.neg_congr ih)

def eulerCharacteristic (K : SimplicialComplexUp) : BEDC.Algebra.Rel.IntegerUp :=
  alternatingSum BEDC.Algebra.Rel.IntegerUp_RelCommRing K.simplexCountByDegree

theorem eulerCharacteristic_congr {xs ys : List BEDC.Algebra.Rel.IntegerUp}
    (paired : ListPairwiseRel BEDC.Algebra.Rel.IntEq xs ys) :
    BEDC.Algebra.Rel.IntEq
      (alternatingSum BEDC.Algebra.Rel.IntegerUp_RelCommRing xs)
      (alternatingSum BEDC.Algebra.Rel.IntegerUp_RelCommRing ys) :=
  alternatingSum_congr BEDC.Algebra.Rel.IntegerUp_RelCommRing paired

structure GeometryCategoryHomologyRows where
  category : Type
  functor : Type
  finiteModule : Type 1
  simplicialComplex : Type
  integerEulerCarrier : BEDC.Algebra.Rel.IntegerUp -> Prop

def geometryCategoryHomologyRows : GeometryCategoryHomologyRows where
  category := CategoryUp
  functor := Sigma fun C : CategoryUp => Sigma fun D : CategoryUp => FunctorUp C D
  finiteModule :=
    Sigma fun RCarrier : Type =>
      Sigma fun RE : RelEquiv RCarrier =>
        Sigma fun R : RingUp RCarrier RE => FiniteModuleUp RCarrier RE R
  simplicialComplex := SimplicialComplexUp
  integerEulerCarrier := fun z => BEDC.Algebra.Rel.IntEq z z

theorem geometryCategoryHomologyRows_integerEulerCarrier
    (z : BEDC.Algebra.Rel.IntegerUp) :
    geometryCategoryHomologyRows.integerEulerCarrier z :=
  BEDC.Algebra.Rel.IntegerUp_RelCommRing.refl z

end BEDC.Algebra.Spine.GeometryCategoryHomology
