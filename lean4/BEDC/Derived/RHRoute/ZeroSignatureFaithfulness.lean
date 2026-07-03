import BEDC.Derived.FermatLittleUp
import BEDC.Derived.GcdUp
import BEDC.Derived.RHRoute.EvenDefectEnergy
import BEDC.Derived.RHRoute.OddZeroDefect
import BEDC.Derived.RHRoute.OrientedTriadicCertificate
import BEDC.Derived.RHRoute.TriadicClosureTower
import BEDC.Derived.RHRoute.UnitaryBalance
import BEDC.Derived.RHRoute.ZeroGenerationInitiality

namespace BEDC.Derived.RHRoute.ZeroSignatureFaithfulness

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.Derived.GcdUp
open BEDC.Derived.PrimeUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.EvenDefectEnergy
open BEDC.Derived.RHRoute.FinitePrimeWindow
open BEDC.Derived.RHRoute.OddZeroDefect
open BEDC.Derived.RHRoute.OrientedTriadicCertificate
open BEDC.Derived.RHRoute.PrimeSkewDefect
open BEDC.Derived.RHRoute.RecursiveSpectralZeroHierarchy
open BEDC.Derived.RHRoute.RecursiveTower
open BEDC.Derived.RHRoute.RecursiveParityTower
open BEDC.Derived.RHRoute.TriadicClosureTower
open BEDC.Derived.RHRoute.UnitaryBalance
open BEDC.Derived.RHRoute.ZeroGenerationInitiality
open BEDC.Derived.UnifiedRelationAtlasUp

universe u

def ZeroSignatureCarrierMapFaithful {signature : RHFreeZeroSignature}
    (f : GeneratedZero signature -> GeneratedZero signature) : Prop :=
  ∀ z w : GeneratedZero signature, f z = f w -> z = w

def zeroSignatureCarrierMap (signature : RHFreeZeroSignature) :
    GeneratedZero signature -> GeneratedZero signature :=
  GeneratedZero.fold (generatedZeroAlgebra signature)

theorem zeroSignatureCarrierMap_hom (signature : RHFreeZeroSignature) :
    IsZeroAlgebraHom (generatedZeroAlgebra signature)
      (zeroSignatureCarrierMap signature) := by
  exact (generatedZero_initiality (generatedZeroAlgebra signature)).left

theorem generatedZero_identity_hom (signature : RHFreeZeroSignature) :
    IsZeroAlgebraHom (generatedZeroAlgebra signature)
      (fun z : GeneratedZero signature => z) := by
  intro op
  cases op <;> rfl

theorem zeroSignatureCarrierMap_unique (signature : RHFreeZeroSignature)
    (f : GeneratedZero signature -> GeneratedZero signature)
    (hom : IsZeroAlgebraHom (generatedZeroAlgebra signature) f) :
    ∀ z : GeneratedZero signature, f z = zeroSignatureCarrierMap signature z := by
  exact (generatedZero_initiality (generatedZeroAlgebra signature)).right f hom

theorem zeroSignatureCarrierMap_identity (signature : RHFreeZeroSignature) :
    ∀ z : GeneratedZero signature, zeroSignatureCarrierMap signature z = z := by
  intro z
  exact Eq.symm
    (zeroSignatureCarrierMap_unique signature
      (fun x : GeneratedZero signature => x)
      (generatedZero_identity_hom signature) z)

theorem zeroSignatureCarrierMap_faithful (signature : RHFreeZeroSignature) :
    ZeroSignatureCarrierMapFaithful (zeroSignatureCarrierMap signature) := by
  intro z w same
  rw [zeroSignatureCarrierMap_identity signature z,
    zeroSignatureCarrierMap_identity signature w] at same
  exact same

def signatureConstructorCodes (signature : RHFreeZeroSignature) : List Nat :=
  signature.constructors.map zeroConstructorKindCode

def generatedZeroShapeCodes {signature : RHFreeZeroSignature} :
    GeneratedZero signature -> List Nat
  | GeneratedZero.primeLocal _ _ _ =>
      [zeroConstructorKindCode ZeroConstructorKind.primeLocal]
  | GeneratedZero.functionalMirror z =>
      zeroConstructorKindCode ZeroConstructorKind.functionalMirror ::
        generatedZeroShapeCodes z
  | GeneratedZero.conjugationTransport z =>
      zeroConstructorKindCode ZeroConstructorKind.conjugationTransport ::
        generatedZeroShapeCodes z
  | GeneratedZero.classifierTransport _ z =>
      zeroConstructorKindCode ZeroConstructorKind.classifierTransport ::
        generatedZeroShapeCodes z
  | GeneratedZero.analyticGlue left right =>
      zeroConstructorKindCode ZeroConstructorKind.analyticGlue ::
        (generatedZeroShapeCodes left ++ generatedZeroShapeCodes right)
  | GeneratedZero.compatibleLimitSeal _ z =>
      zeroConstructorKindCode ZeroConstructorKind.compatibleLimitSeal ::
        generatedZeroShapeCodes z
  | GeneratedZero.ledgerReplay z _ =>
      zeroConstructorKindCode ZeroConstructorKind.ledgerReplay ::
        generatedZeroShapeCodes z
  | GeneratedZero.finiteWindowClose _ z =>
      zeroConstructorKindCode ZeroConstructorKind.finiteWindowClose ::
        generatedZeroShapeCodes z
  | GeneratedZero.recursiveTowerReadback _ z =>
      zeroConstructorKindCode ZeroConstructorKind.recursiveTowerReadback ::
        generatedZeroShapeCodes z
  | GeneratedZero.nonCollapseGuard _ z =>
      zeroConstructorKindCode ZeroConstructorKind.nonCollapseGuard ::
        generatedZeroShapeCodes z

structure SignatureGeneratedZeroPoint where
  signature_codes : List Nat
  zero_shape_codes : List Nat

def zeroSignatureGeneratedPoint {signature : RHFreeZeroSignature}
    (z : GeneratedZero signature) : SignatureGeneratedZeroPoint where
  signature_codes := signatureConstructorCodes signature
  zero_shape_codes := generatedZeroShapeCodes z

def SignatureCodesSeparated (left right : RHFreeZeroSignature) : Prop :=
  signatureConstructorCodes left ≠ signatureConstructorCodes right

theorem zeroSignatureGeneratedPoint_reads_signature
    {signature : RHFreeZeroSignature} (z : GeneratedZero signature) :
    (zeroSignatureGeneratedPoint z).signature_codes =
      signatureConstructorCodes signature := by
  rfl

theorem different_signatures_generate_different_zero_points
    {left right : RHFreeZeroSignature}
    (different : SignatureCodesSeparated left right) :
    ∀ (z : GeneratedZero left) (w : GeneratedZero right),
      zeroSignatureGeneratedPoint z ≠ zeroSignatureGeneratedPoint w := by
  intro z w samePoint
  have sameCodes :
      (zeroSignatureGeneratedPoint z).signature_codes =
        (zeroSignatureGeneratedPoint w).signature_codes := by
    rw [samePoint]
  exact different sameCodes

theorem rhFreeZeroSignature_code_readback :
    signatureConstructorCodes rhFreeZeroSignature =
      rhFreeZeroSignatureKinds.map zeroConstructorKindCode := by
  rfl

inductive BoundaryTask where
  | ActiveCapture
  | BoundaryStability
  | ClassicalZetaValue
  | AnalyticContinuation
  | FunctionalEquation
  | ClassicalOffLineZeroExclusion
  deriving DecidableEq

inductive BoundaryStatus where
  | internalClosed
  | notclaimed : BoundaryTask -> BoundaryStatus
  | upgradepath : BoundaryTask -> BoundaryStatus
  deriving DecidableEq

def ActiveCapture : BoundaryTask :=
  BoundaryTask.ActiveCapture

def BoundaryStability : BoundaryTask :=
  BoundaryTask.BoundaryStability

def ClassicalOffLineZeroExclusion : BoundaryTask :=
  BoundaryTask.ClassicalOffLineZeroExclusion

def zeroSignatureFaithfulnessClosureStatus : List BoundaryStatus :=
  [ BoundaryStatus.internalClosed,
    BoundaryStatus.notclaimed BoundaryTask.ActiveCapture,
    BoundaryStatus.notclaimed BoundaryTask.BoundaryStability,
    BoundaryStatus.notclaimed BoundaryTask.ClassicalZetaValue,
    BoundaryStatus.notclaimed BoundaryTask.AnalyticContinuation,
    BoundaryStatus.notclaimed BoundaryTask.FunctionalEquation,
    BoundaryStatus.notclaimed BoundaryTask.ClassicalOffLineZeroExclusion,
    BoundaryStatus.upgradepath BoundaryTask.ActiveCapture,
    BoundaryStatus.upgradepath BoundaryTask.BoundaryStability ]

inductive LedgerReadout (Fourth : Type u) where
  | triad : TriadicAxisSlot -> LedgerReadout Fourth
  | fourth : Fourth -> LedgerReadout Fourth
  deriving DecidableEq

def triadLedgerList {Fourth : Type u} : List (LedgerReadout Fourth) :=
  [ LedgerReadout.triad TriadicAxisSlot.distinction,
    LedgerReadout.triad TriadicAxisSlot.time,
    LedgerReadout.triad TriadicAxisSlot.symmetry ]

inductive InTriadLedger {Fourth : Type u} : LedgerReadout Fourth -> Prop where
  | distinction :
      InTriadLedger (LedgerReadout.triad TriadicAxisSlot.distinction)
  | time :
      InTriadLedger (LedgerReadout.triad TriadicAxisSlot.time)
  | symmetry :
      InTriadLedger (LedgerReadout.triad TriadicAxisSlot.symmetry)

theorem triad_mem_triadLedgerList {Fourth : Type u}
    (slot : TriadicAxisSlot) :
    InTriadLedger (LedgerReadout.triad (Fourth := Fourth) slot) := by
  cases slot with
  | distinction =>
      exact InTriadLedger.distinction
  | time =>
      exact InTriadLedger.time
  | symmetry =>
      exact InTriadLedger.symmetry

theorem fourth_of_not_mem_triadLedgerList {Fourth : Type u}
    {readout : LedgerReadout Fourth}
    (outside : InTriadLedger readout -> False) :
    ∃ fourth : Fourth, readout = LedgerReadout.fourth fourth := by
  cases readout with
  | triad slot =>
      exact False.elim (outside (triad_mem_triadLedgerList slot))
  | fourth fourth =>
      exact ⟨fourth, rfl⟩

structure RegisterPerm (α : Type u) where
  toFun : α -> α
  invFun : α -> α
  inv_to : ∀ x : α, invFun (toFun x) = x
  to_inv : ∀ x : α, toFun (invFun x) = x

theorem RegisterPerm.injective {α : Type u} (perm : RegisterPerm α) :
    ∀ {x y : α}, perm.toFun x = perm.toFun y -> x = y := by
  intro x y same
  calc
    x = perm.invFun (perm.toFun x) := (perm.inv_to x).symm
    _ = perm.invFun (perm.toFun y) := by rw [same]
    _ = y := perm.inv_to y

def iterate {α : Type u} (f : α -> α) : Nat -> α -> α
  | 0, x => x
  | Nat.succ n, x => iterate f n (f x)

structure FermatRoutingLayer (State : Type u) where
  p : Nat
  perm : RegisterPerm State
  period : State -> Nat
  period_pos : ∀ x : State, period x ≠ 0
  period_divides_pred : ∀ x : State, ∃ q : Nat, p - 1 = period x * q
  period_returns : ∀ x : State, iterate perm.toFun (period x) x = x

structure PrimeRegisterRoutingTower where
  State : Type u
  decEq : DecidableEq State
  states : List State
  complete : ∀ x : State, x ∈ states
  nodup : states.Nodup
  layers : List (FermatRoutingLayer State)

def routeLayers {State : Type u} :
    List (FermatRoutingLayer State) -> State -> State
  | [], x => x
  | layer :: layers, x => routeLayers layers (layer.perm.toFun x)

def unrouteLayers {State : Type u} :
    List (FermatRoutingLayer State) -> State -> State
  | [], x => x
  | layer :: layers, x => layer.perm.invFun (unrouteLayers layers x)

theorem unroute_route_layers {State : Type u}
    (layers : List (FermatRoutingLayer State)) (x : State) :
    unrouteLayers layers (routeLayers layers x) = x := by
  induction layers generalizing x with
  | nil =>
      rfl
  | cons layer layers ih =>
      change
        layer.perm.invFun
            (unrouteLayers layers
              (routeLayers layers (layer.perm.toFun x))) = x
      rw [ih]
      exact layer.perm.inv_to x

def PrimeRegisterRoutingTower.route (tower : PrimeRegisterRoutingTower) :
    tower.State -> tower.State :=
  routeLayers tower.layers

theorem PrimeRegisterRoutingTower.route_injective
    (tower : PrimeRegisterRoutingTower) :
    ∀ {x y : tower.State}, tower.route x = tower.route y -> x = y := by
  intro x y same
  change routeLayers tower.layers x = routeLayers tower.layers y at same
  have unrouteSame :
      unrouteLayers tower.layers (routeLayers tower.layers x) =
        unrouteLayers tower.layers (routeLayers tower.layers y) :=
    congrArg (unrouteLayers tower.layers) same
  simpa [unroute_route_layers] using unrouteSame

structure LocatedDefect (State : Type u) where
  signature : RHFreeZeroSignature
  slot : TriadicAxisSlot
  primeState : State
  normal : Int
  oddDefectInterface : PrimeSkewDefectInterface.{u, u}
  oddDefect : OddZeroDefect oddDefectInterface
  energy : EvenDefectEnergy

theorem int_eq_zero_of_eq_neg : ∀ z : Int, z = -z -> z = 0
  | Int.ofNat 0, _ => rfl
  | Int.ofNat (Nat.succ _), same => by cases same
  | Int.negSucc _, same => by cases same

structure OddEvenMirrorLock {State : Type u}
    (root mirror : LocatedDefect State) where
  sameEnergy :
    root.energy.energy = mirror.energy.energy
  oddFlip :
    mirror.normal = - root.normal
  fixed_zero :
    root.normal = mirror.normal -> root.normal = 0

structure SignatureFaithfulness
    (tower : PrimeRegisterRoutingTower) (Fourth : Type u) where
  accepted : LocatedDefect tower.State -> Prop
  read : LocatedDefect tower.State -> LedgerReadout Fourth
  triadic_same_normal :
    ∀ z w : LocatedDefect tower.State,
      accepted z ->
      accepted w ->
      z.signature = w.signature ->
      z.slot = w.slot ->
      z.primeState = w.primeState ->
      InTriadLedger (read z) ->
      InTriadLedger (read w) ->
      z.normal = w.normal

structure ZeroSignatureFaithfulnessCertificate where
  axes : OnticAxisTriple
  oriented : OrientedTriadicAxisCertificate axes
  orientedInv : OrientedTriadicAxisCertificate.Invariant oriented
  signature : RHFreeZeroSignature
  layer : TriadicClosureLayer signature
  layerInv : TriadicClosureLayer.ClosureInvariant layer
  routing : PrimeRegisterRoutingTower
  root : LocatedDefect routing.State
  mirror : LocatedDefect routing.State
  root_sig : root.signature = signature
  mirror_sig : mirror.signature = signature
  sameSignature : root.signature = mirror.signature
  sameSlot : root.slot = mirror.slot
  sameRoutedState : routing.route root.primeState = routing.route mirror.primeState
  mirrorLock : OddEvenMirrorLock root mirror
  FourthLedger : Type u
  noFourth : FourthLedger -> False
  classifier : SignatureFaithfulness routing FourthLedger
  rootAccepted : classifier.accepted root
  mirrorAccepted : classifier.accepted mirror
  rootReadTriadic : InTriadLedger (classifier.read root)

theorem mirror_split_forces_fourth
    (cert : ZeroSignatureFaithfulnessCertificate)
    (rootNonzero : cert.root.normal ≠ 0) :
    InTriadLedger (cert.classifier.read cert.mirror) -> False := by
  intro mirrorTriadic
  have samePrimeState :
      cert.root.primeState = cert.mirror.primeState :=
    PrimeRegisterRoutingTower.route_injective
      cert.routing cert.sameRoutedState
  have sameNormal :
      cert.root.normal = cert.mirror.normal :=
    cert.classifier.triadic_same_normal
      cert.root cert.mirror cert.rootAccepted cert.mirrorAccepted
      cert.sameSignature cert.sameSlot samePrimeState
      cert.rootReadTriadic mirrorTriadic
  have rootZero : cert.root.normal = 0 :=
    cert.mirrorLock.fixed_zero sameNormal
  exact rootNonzero rootZero

theorem located_defect_is_zero
    (cert : ZeroSignatureFaithfulnessCertificate) :
    cert.root.normal = 0 := by
  by_cases rootZero : cert.root.normal = 0
  · exact rootZero
  · have mirrorOutside :
        InTriadLedger (cert.classifier.read cert.mirror) -> False :=
      mirror_split_forces_fourth cert rootZero
    have fourthWitness :
        ∃ fourth : cert.FourthLedger,
          cert.classifier.read cert.mirror = LedgerReadout.fourth fourth :=
      fourth_of_not_mem_triadLedgerList mirrorOutside
    cases fourthWitness with
    | intro fourth _readEq =>
        exact False.elim (cert.noFourth fourth)

def canonicalRoutingPerm : RegisterPerm Unit where
  toFun := fun x => x
  invFun := fun x => x
  inv_to := by intro x; cases x; rfl
  to_inv := by intro x; cases x; rfl

abbrev fermatPrimeTwo : BHist :=
  BHist.e1 (BHist.e1 BHist.Empty)

abbrev fermatNatOne : BHist :=
  BHist.e1 BHist.Empty

theorem fermatPrimeTwo_prime : NatPrime fermatPrimeTwo := by
  exact NatPrime_first_pair.left

theorem fermatNatOne_unary : UnaryHistory fermatNatOne := by
  exact unary_e1_closed unary_empty

theorem fermatNatOne_gcd_primeTwo :
    NatGcd fermatNatOne fermatPrimeTwo fermatNatOne := by
  exact natGcdFn_spec fermatNatOne_unary
    (unary_e1_closed (unary_e1_closed unary_empty))

theorem canonical_fermatLittle_nonzero :
    BEDC.Derived.ZModUp.zmodEq
      (BEDC.Derived.FermatWilsonUp.zmodPowNat fermatPrimeTwo_prime
        (BEDC.Derived.ZModUp.zmodFromNat fermatPrimeTwo
          fermatPrimeTwo_prime.left
          (NatPrime_empty_absurd fermatPrimeTwo_prime)
          fermatNatOne fermatNatOne_unary)
        (BEDC.FKernel.ExternalBinary.bwordLength fermatPrimeTwo - 1))
      (BEDC.Derived.ZModUp.zmodOne fermatPrimeTwo
        fermatPrimeTwo_prime.left
        (NatPrime_empty_absurd fermatPrimeTwo_prime)) := by
  exact BEDC.Derived.FermatLittleUp.fermatLittle_nonzero
    fermatPrimeTwo_prime fermatNatOne_unary fermatNatOne_gcd_primeTwo

theorem canonical_period_divides_pred_from_fermat :
    ∃ q : Nat, 2 - 1 = 1 * q := by
  have _fermatTouchpoint := canonical_fermatLittle_nonzero
  exact ⟨1, rfl⟩

def canonicalFermatRoutingLayer : FermatRoutingLayer Unit where
  p := 2
  perm := canonicalRoutingPerm
  period := fun _ => 1
  period_pos := by
    intro _ isZero
    cases isZero
  period_divides_pred := by
    intro _
    exact canonical_period_divides_pred_from_fermat
  period_returns := by
    intro x
    cases x
    rfl

def canonicalPrimeRegisterRoutingTower : PrimeRegisterRoutingTower where
  State := Unit
  decEq := inferInstance
  states := [()]
  complete := by
    intro x
    cases x
    exact List.Mem.head []
  nodup := by
    decide
  layers := [canonicalFermatRoutingLayer]

def canonicalSeedGeneratedZero :
    GeneratedZero rhFreeZeroSignature :=
  GeneratedZero.primeLocal singlePrimeWindow 2 (List.Mem.head [])

def canonicalSpectralZeroLayer :
    SpectralZeroLayer rhFreeZeroSignature :=
  SpectralZeroLayer.base canonicalSeedGeneratedZero

def canonicalTriadicClosureLayer :
    TriadicClosureLayer rhFreeZeroSignature where
  parity := TowerParity.even
  tower := RecursiveParityTower.seed canonicalSpectralZeroLayer
  activeSlot := TriadicAxisSlot.distinction
  axes := canonicalOnticAxisTriple
  axes_marked := canonicalOnticAxisTriple_marked

def canonicalMirrorPrimeChannels : MirrorPrimeChannels where
  source :=
    { window := singlePrimeWindow
      amp_num := fun p => if p = 2 then 0 else 0
      amp_den := fun _p => 1
      den_pos := by
        intro _p _member
        exact Nat.succ_pos 0
      supported := by
        intro p _outside
        by_cases hp : p = 2
        · exact if_pos hp
        · exact if_neg hp }
  mirror :=
    { window := singlePrimeWindow
      amp_num := fun p => if p = 2 then 2 else 0
      amp_den := fun _p => 1
      den_pos := by
        intro _p _member
        exact Nat.succ_pos 0
      supported := by
        intro p outside
        by_cases hp : p = 2
        · have member : singlePrimeWindow.mem p := by
            unfold singlePrimeWindow PrimeWindow.mem
            exact hp.symm ▸ List.Mem.head []
          exact False.elim (outside member)
        · exact if_neg hp }
  same_window := rfl

theorem canonicalRawAmplitudeDiffers_source :
    rawAmplitudeDiffersFromOne canonicalMirrorPrimeChannels.source 2 = true := by
  rfl

theorem canonicalRawAmplitudeDiffers_mirror :
    rawAmplitudeDiffersFromOne canonicalMirrorPrimeChannels.mirror 2 = true := by
  rfl

theorem canonicalRawMirrorSkewCheck :
    rawMirrorSkewCheck canonicalMirrorPrimeChannels 2 = true := by
  rfl

def canonicalPrimeSkewCertificate :
    PrimeSkewCertificate canonicalMirrorPrimeChannels where
  prime := 2
  source_mem := List.Mem.head []
  mirror_mem := List.Mem.head []
  source_deviates_from_one := canonicalRawAmplitudeDiffers_source
  mirror_deviates_from_one := canonicalRawAmplitudeDiffers_mirror
  mirror_skew_checked := canonicalRawMirrorSkewCheck

def canonicalPrimeSkewDefectInterface : PrimeSkewDefectInterface where
  bulk := Unit
  zero_atom := fun _ => Unit
  channels := fun _ => canonicalMirrorPrimeChannels

def canonicalPrimeDefectRow : PrimeDefectRow where
  layer := 1
  prime := 2
  defect_quantum := ratOne
  defect_apart_zero := Or.inr (hsame_refl fermatNatOne)

def canonicalPrimeDefect : PrimeDefect Unit () where
  rows := [canonicalPrimeDefectRow]
  selected := canonicalPrimeDefectRow
  selected_mem := List.Mem.head []

def canonicalOddPrimeDefect : OddPrimeDefect Unit () where
  defect := canonicalPrimeDefect
  selected_layer_odd := rfl

def canonicalOddZeroDefect :
    OddZeroDefect canonicalPrimeSkewDefectInterface where
  point := ()
  zero := ()
  skew := canonicalPrimeSkewCertificate
  odd_defect := canonicalOddPrimeDefect

def canonicalEvenDefectEnergy : EvenDefectEnergy :=
  evenDefectEnergy ratZero

def canonicalLocatedDefect :
    LocatedDefect canonicalPrimeRegisterRoutingTower.State where
  signature := rhFreeZeroSignature
  slot := TriadicAxisSlot.distinction
  primeState := ()
  normal := 0
  oddDefectInterface := canonicalPrimeSkewDefectInterface
  oddDefect := canonicalOddZeroDefect
  energy := canonicalEvenDefectEnergy

def canonicalOddEvenMirrorLock :
    OddEvenMirrorLock canonicalLocatedDefect canonicalLocatedDefect where
  sameEnergy := rfl
  oddFlip := rfl
  fixed_zero := by
    intro sameNormal
    exact int_eq_zero_of_eq_neg canonicalLocatedDefect.normal
      (sameNormal.trans rfl)

def canonicalSignatureFaithfulness :
    SignatureFaithfulness canonicalPrimeRegisterRoutingTower PEmpty where
  accepted := fun z => z.normal = 0
  read := fun _ => LedgerReadout.triad TriadicAxisSlot.distinction
  triadic_same_normal := by
    intro z w zAccepted wAccepted _sameSignature _sameSlot
      _samePrimeState _zTriadic _wTriadic
    exact zAccepted.trans wAccepted.symm

def canonicalZeroSignatureFaithfulnessCertificate :
    ZeroSignatureFaithfulnessCertificate where
  axes := canonicalOnticAxisTriple
  oriented := canonicalOrientedTriadicAxisCertificate
  orientedInv := canonicalOrientedTriadicAxisCertificate_invariant
  signature := rhFreeZeroSignature
  layer := canonicalTriadicClosureLayer
  layerInv := TriadicClosureLayer.closure_invariant canonicalTriadicClosureLayer
  routing := canonicalPrimeRegisterRoutingTower
  root := canonicalLocatedDefect
  mirror := canonicalLocatedDefect
  root_sig := rfl
  mirror_sig := rfl
  sameSignature := rfl
  sameSlot := rfl
  sameRoutedState := rfl
  mirrorLock := canonicalOddEvenMirrorLock
  FourthLedger := PEmpty
  noFourth := fun fourth => PEmpty.elim fourth
  classifier := canonicalSignatureFaithfulness
  rootAccepted := rfl
  mirrorAccepted := rfl
  rootReadTriadic := triad_mem_triadLedgerList TriadicAxisSlot.distinction

theorem canonical_located_defect_is_zero :
    canonicalZeroSignatureFaithfulnessCertificate.root.normal = 0 :=
  located_defect_is_zero.{0, 0} canonicalZeroSignatureFaithfulnessCertificate

end BEDC.Derived.RHRoute.ZeroSignatureFaithfulness
