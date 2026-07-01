/-!
# Observation section coherence packet

This module records the formal core of the quantum-gravity vision packet as a
structural BEDC object.  The observation ledger is an append-only generation
order; it is not Schrodinger time, proper time, or coordinate time.  The
section-bundle layer is a category-to-category functor.  Pair-indexed transport
without a morphism index is recorded as a resolution requirement: either the
base is thin, or a canonical transport selector is supplied.

The file proves only structural coherence.  It does not derive physical
dynamics, Einstein equations, Schrodinger equations, or a physical
identification between observation generation order and physical time.
-/

namespace BEDC.Derived.Visions.ObservationSectionCoherence

universe u v w x y z

/-- A finite append-only observation ledger over witness rows `W`. -/
abbrev Ledger (W : Type u) : Type u :=
  List W

/-- Right-append prefix order on finite ledgers. -/
def prefixLe {W : Type u} (l l' : Ledger W) : Prop :=
  exists d : Ledger W, l' = l ++ d

private theorem append_nil_right {W : Type u} :
    forall l : Ledger W, l ++ ([] : Ledger W) = l := by
  intro l
  induction l with
  | nil =>
      rfl
  | cons head tail ih =>
      change head :: (tail ++ ([] : Ledger W)) = head :: tail
      exact congrArg (List.cons head) ih

private theorem append_assoc_right {W : Type u} :
    forall a b c : Ledger W, (a ++ b) ++ c = a ++ (b ++ c) := by
  intro a b c
  induction a with
  | nil =>
      rfl
  | cons head tail ih =>
      change head :: ((tail ++ b) ++ c) = head :: (tail ++ (b ++ c))
      exact congrArg (List.cons head) ih

/-- The append-only prefix relation is reflexive. -/
theorem prefixLe_refl {W : Type u} (l : Ledger W) :
    prefixLe l l := by
  exists ([] : Ledger W)
  exact (append_nil_right l).symm

/-- The append-only prefix relation is transitive. -/
theorem prefixLe_trans {W : Type u} {l l' l'' : Ledger W} :
    prefixLe l l' -> prefixLe l' l'' -> prefixLe l l'' := by
  intro hll' hl'l''
  cases hll' with
  | intro d hd =>
      cases hl'l'' with
      | intro e he =>
          exists d ++ e
          calc
            l'' = l' ++ e := he
            _ = (l ++ d) ++ e := congrArg (fun q : Ledger W => q ++ e) hd
            _ = l ++ (d ++ e) := append_assoc_right l d e

/-- Observation-generation stages, kept separate from physical time notions. -/
structure ObservationPreorder where
  Stage : Type u
  le : Stage -> Stage -> Prop
  le_refl : forall t : Stage, le t t
  le_trans : forall {t u v : Stage}, le t u -> le u v -> le t v

/-- An append-only observation log over an observation-generation preorder. -/
structure Log (T : ObservationPreorder.{u}) (W : Type v) where
  toLedger : T.Stage -> Ledger W
  monotone : forall {t u : T.Stage}, T.le t u -> prefixLe (toLedger t) (toLedger u)

/-- Field projection theorem for append-only log monotonicity. -/
theorem log_monotone {T : ObservationPreorder.{u}} {W : Type v}
    (L : Log T W) {t u : T.Stage} :
    T.le t u -> prefixLe (L.toLedger t) (L.toLedger u) := by
  intro htu
  exact L.monotone htu

/-- A small first-principles category record for frame comparisons. -/
structure FrameCat where
  Obj : Type u
  Hom : Obj -> Obj -> Type v
  id : forall R : Obj, Hom R R
  comp : forall {R S U : Obj}, Hom S U -> Hom R S -> Hom R U
  assoc :
    forall {R S U V : Obj} (h : Hom U V) (g : Hom S U) (f : Hom R S),
      comp h (comp g f) = comp (comp h g) f
  id_left :
    forall {R S : Obj} (f : Hom R S), comp (id S) f = f
  id_right :
    forall {R S : Obj} (f : Hom R S), comp f (id R) = f

/-- Hilbert-like category skeleton.  No Hilbert analysis is claimed here. -/
structure HilbertLikeCat where
  Obj : Type u
  Hom : Obj -> Obj -> Type v
  id : forall H : Obj, Hom H H
  comp : forall {H K L : Obj}, Hom K L -> Hom H K -> Hom H L
  assoc :
    forall {H K L M : Obj} (h : Hom L M) (g : Hom K L) (f : Hom H K),
      comp h (comp g f) = comp (comp h g) f
  id_left :
    forall {H K : Obj} (f : Hom H K), comp (id K) f = f
  id_right :
    forall {H K : Obj} (f : Hom H K), comp f (id H) = f

/-- Carrier name for the object side of the Hilbert-like target category. -/
abbrev HilbertLikeCarrier (H : HilbertLikeCat.{u, v}) : Type u :=
  H.Obj

/-- Section-bundle packet as a functor from frames to Hilbert-like carriers. -/
structure SectionBundleFunctor
    (F : FrameCat.{u, v}) (H : HilbertLikeCat.{w, x}) where
  objMap : F.Obj -> HilbertLikeCarrier H
  homMap :
    forall {R S : F.Obj}, F.Hom R S -> H.Hom (objMap R) (objMap S)
  map_comp :
    forall {R S U : F.Obj} (g : F.Hom S U) (f : F.Hom R S),
      homMap (F.comp g f) = H.comp (homMap g) (homMap f)
  map_id :
    forall R : F.Obj, homMap (F.id R) = H.id (objMap R)

/-- Projection theorem for section-bundle composition functoriality. -/
theorem sectionBundleFunctor_comp
    {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
    (Phi : SectionBundleFunctor F H)
    {R S U : F.Obj} (g : F.Hom S U) (f : F.Hom R S) :
    Phi.homMap (F.comp g f) = H.comp (Phi.homMap g) (Phi.homMap f) := by
  exact Phi.map_comp g f

/-- Projection theorem for identity transport functoriality. -/
theorem sectionBundleFunctor_id
    {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
    (Phi : SectionBundleFunctor F H) (R : F.Obj) :
    Phi.homMap (F.id R) = H.id (Phi.objMap R) := by
  exact Phi.map_id R

/-- Thin base: each ordered pair of frames has at most one comparison morphism. -/
def ThinBase (F : FrameCat.{u, v}) : Prop :=
  forall R S : F.Obj, forall f g : F.Hom R S, f = g

/-- A pair of distinct parallel frame morphisms witnesses the non-thin gap. -/
def HasParallelMorphisms (F : FrameCat.{u, v}) : Prop :=
  exists R : F.Obj, exists S : F.Obj, exists f : F.Hom R S, exists g : F.Hom R S,
    Not (f = g)

/-- Canonical transport data chooses one representative for each inhabited pair. -/
structure CanonicalTransport (F : FrameCat.{u, v}) where
  choose : forall {R S : F.Obj}, F.Hom R S -> F.Hom R S
  stable :
    forall {R S : F.Obj} (f g : F.Hom R S), choose f = choose g

/--
Pair-indexed transport without a morphism index is well-defined only after the
source ambiguity is resolved: either the base is thin, or canonical transport
data is supplied.  Without this resolution a notation like `Phi_{S <- R}`
hides possible path dependence, holonomy, or gauge phase.
-/
def PairIndexedTransportWellDefined (F : FrameCat.{u, v}) : Prop :=
  ThinBase F or Nonempty (CanonicalTransport F)

/-- The formal gap criterion for morphism-free pair-indexed transport notation. -/
theorem pairIndexed_wellDefined_iff_thin_or_canonical
    (F : FrameCat.{u, v}) :
    PairIndexedTransportWellDefined F <->
      ThinBase F or Nonempty (CanonicalTransport F) := by
  constructor
  · intro h
    exact h
  · intro h
    exact h

/-- Thin bases make every section-bundle transport pair-indexed on the target. -/
theorem pairIndexed_phi_wellDefined_of_thin
    {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
    (Phi : SectionBundleFunctor F H) :
    ThinBase F ->
      forall {R S : F.Obj} (f g : F.Hom R S), Phi.homMap f = Phi.homMap g := by
  intro hthin R S f g
  exact congrArg Phi.homMap (hthin R S f g)

/-- Canonical transport makes the selected representative pair-indexed. -/
theorem pairIndexed_phi_wellDefined_of_canonical
    {F : FrameCat.{u, v}} {H : HilbertLikeCat.{w, x}}
    (Phi : SectionBundleFunctor F H) (canon : CanonicalTransport F) :
    forall {R S : F.Obj} (f g : F.Hom R S),
      Phi.homMap (canon.choose f) = Phi.homMap (canon.choose g) := by
  intro R S f g
  exact congrArg Phi.homMap (canon.stable f g)

/-- Parallel distinct morphisms refute thinness. -/
theorem not_thin_of_parallel_morphisms {F : FrameCat.{u, v}} :
    HasParallelMorphisms F -> Not (ThinBase F) := by
  intro hgap hthin
  cases hgap with
  | intro R rest =>
      cases rest with
      | intro S rest' =>
          cases rest' with
          | intro f rest'' =>
              cases rest'' with
              | intro g hneq =>
                  exact hneq (hthin R S f g)

/-- If the base is non-thin and no canonical selector is supplied, the gap remains. -/
theorem pairIndexed_gap_without_resolution {F : FrameCat.{u, v}} :
    HasParallelMorphisms F ->
      Not (Nonempty (CanonicalTransport F)) ->
        Not (PairIndexedTransportWellDefined F) := by
  intro hgap hnoCanon hwell
  have hor :
      ThinBase F or Nonempty (CanonicalTransport F) :=
    (pairIndexed_wellDefined_iff_thin_or_canonical F).mp hwell
  cases hor with
  | inl hthin =>
      exact (not_thin_of_parallel_morphisms hgap) hthin
  | inr hcanon =>
      exact hnoCanon hcanon

/--
Grounded observation-section system.  The fibre/base/time language is schematic:
the fibre is only Hilbert-like structure, the base is only frame comparison, and
the observation preorder is only append-only witness generation.
-/
structure ObservationSectionSystem (W : Type z) where
  frameCat : FrameCat.{u, v}
  hilbertCat : HilbertLikeCat.{w, x}
  sectionFunctor : SectionBundleFunctor frameCat hilbertCat
  observation : ObservationPreorder.{y}
  frameHistory : observation.Stage -> frameCat.Obj
  log : Log observation W

/-- Append-only coherence along a two-step observation chain. -/
theorem observation_log_chain
    {W : Type z} (S : ObservationSectionSystem.{u, v, w, x, y, z} W)
    {t u v : S.observation.Stage} :
    S.observation.le t u ->
      S.observation.le u v ->
        prefixLe (S.log.toLedger t) (S.log.toLedger v) := by
  intro htu huv
  exact prefixLe_trans (S.log.monotone htu) (S.log.monotone huv)

/-- Horizontal transport coherence is exactly the section functor law. -/
theorem observation_section_transport_comp
    {W : Type z} (S : ObservationSectionSystem.{u, v, w, x, y, z} W)
    {t u v : S.observation.Stage}
    (f : S.frameCat.Hom (S.frameHistory t) (S.frameHistory u))
    (g : S.frameCat.Hom (S.frameHistory u) (S.frameHistory v)) :
    S.sectionFunctor.homMap (S.frameCat.comp g f) =
      S.hilbertCat.comp (S.sectionFunctor.homMap g) (S.sectionFunctor.homMap f) := by
  exact S.sectionFunctor.map_comp g f

end BEDC.Derived.Visions.ObservationSectionCoherence
