import BEDC.Derived.CommonCarrierProjectionUp
import BEDC.Derived.MatrixUp
import BEDC.Derived.PolynomialUp

namespace BEDC.Derived.QuarticSpectralCarrierUp

open BEDC.Algebra.Rel
open BEDC.Derived.CommonCarrierProjectionUp
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark

abbrev IntegerUp := BEDC.Derived.PolynomialUp.IntegerUp
abbrev Poly := BEDC.Derived.PolynomialUp.Poly

private abbrev ieq := BEDC.Derived.RationalUp.IntEq
private abbrev iadd := BEDC.Derived.RationalUp.IntAdd
private abbrev imul := BEDC.Derived.RationalUp.IntMul
private abbrev ineg := BEDC.Derived.RationalUp.IntNeg
private abbrev izero := BEDC.Derived.RationalUp.intZero
private abbrev ione := BEDC.Derived.RationalUp.intOne

def emptyProjectionLedger : ProjectionLedger :=
  { observed := []
    observed_nodup := by constructor
    hidden := []
    hidden_nodup := by constructor
    scopedRows := []
    scopedRows_nodup := by constructor
    refused := []
    refused_nodup := by constructor
    transport := []
    transport_nodup := by constructor
    provenance := []
    provenance_nodup := by constructor }

def signedMagnitudeObservation (z : IntegerUp) : BHist :=
  match z.sign with
  | BMark.b0 => BHist.e0 z.magnitude
  | BMark.b1 => BHist.e1 z.magnitude

def intOfNat (n : Nat) : IntegerUp :=
  BEDC.Derived.PolynomialUp.coeffOfNat n

def itwo : IntegerUp := intOfNat 2
def ithree : IntegerUp := intOfNat 3
def ifour : IntegerUp := intOfNat 4
def ieight : IntegerUp := intOfNat 8

def isub (a b : IntegerUp) : IntegerUp :=
  iadd a (ineg b)

def isquare (a : IntegerUp) : IntegerUp :=
  imul a a

def icube (a : IntegerUp) : IntegerUp :=
  imul (isquare a) a

structure QuarticCoefficients where
  c0 : IntegerUp
  c1 : IntegerUp
  c2 : IntegerUp
  c3 : IntegerUp
  c4 : IntegerUp

def QuarticCoefficients.rel (x y : QuarticCoefficients) : Prop :=
  ieq x.c0 y.c0 ∧ ieq x.c1 y.c1 ∧ ieq x.c2 y.c2 ∧
    ieq x.c3 y.c3 ∧ ieq x.c4 y.c4

def QuarticCoefficients.poly (q : QuarticCoefficients) : Poly :=
  [q.c0, q.c1, q.c2, q.c3, q.c4]

def QuarticCoefficients.observations (q : QuarticCoefficients) : List BHist :=
  [signedMagnitudeObservation q.c0, signedMagnitudeObservation q.c1,
    signedMagnitudeObservation q.c2, signedMagnitudeObservation q.c3,
    signedMagnitudeObservation q.c4]

def QuarticCoefficients.admissible (q : QuarticCoefficients) : Prop :=
  BEDC.Derived.PolynomialUp.PolyEq (QuarticCoefficients.poly q)
    [q.c0, q.c1, q.c2, q.c3, q.c4]

def resolventP (q : QuarticCoefficients) : IntegerUp :=
  isub (imul ieight q.c2) (imul ithree (isquare q.c3))

def resolventQ (q : QuarticCoefficients) : IntegerUp :=
  iadd (icube q.c3)
    (iadd (imul ieight q.c1) (ineg (imul ifour (imul q.c3 q.c2))))

def resolventR (q : QuarticCoefficients) : IntegerUp :=
  iadd (imul (isquare q.c3) q.c2)
    (iadd (ineg (imul ifour q.c0)) (ineg (imul q.c3 q.c1)))

def resolventPoly (q : QuarticCoefficients) : Poly :=
  [resolventR q, resolventQ q, resolventP q, ione]

structure ResolventPackage where
  coefficients : QuarticCoefficients
  polynomial : Poly

def resolventPackage (q : QuarticCoefficients) : ResolventPackage :=
  { coefficients := q
    polynomial := resolventPoly q }

def companionBlockTop (_ : QuarticCoefficients) : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := izero
    a01 := ione
    a10 := izero
    a11 := izero }

def companionBlockBottom (q : QuarticCoefficients) : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := ineg q.c0
    a01 := ineg q.c1
    a10 := ione
    a11 := ineg q.c2 }

structure CompanionPackage where
  coefficients : QuarticCoefficients
  topBlock : BEDC.Derived.MatrixUp.Mat2
  bottomBlock : BEDC.Derived.MatrixUp.Mat2

def companionPackage (q : QuarticCoefficients) : CompanionPackage :=
  { coefficients := q
    topBlock := companionBlockTop q
    bottomBlock := companionBlockBottom q }

inductive SpectralProjection where
  | resolvent
  | companion

def QuarticCoefficientsRelEquiv : RelEquiv QuarticCoefficients where
  rel := QuarticCoefficients.rel
  refl := by
    intro x
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_refl x.c0,
        BEDC.Derived.RationalUp.IntEq_refl x.c1,
        BEDC.Derived.RationalUp.IntEq_refl x.c2,
        BEDC.Derived.RationalUp.IntEq_refl x.c3,
        BEDC.Derived.RationalUp.IntEq_refl x.c4⟩
  symm := by
    intro x y same
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_symm same.left,
        BEDC.Derived.RationalUp.IntEq_symm same.right.left,
        BEDC.Derived.RationalUp.IntEq_symm same.right.right.left,
        BEDC.Derived.RationalUp.IntEq_symm same.right.right.right.left,
        BEDC.Derived.RationalUp.IntEq_symm same.right.right.right.right⟩
  trans := by
    intro x y z xy yz
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_trans xy.left yz.left,
        BEDC.Derived.RationalUp.IntEq_trans xy.right.left yz.right.left,
        BEDC.Derived.RationalUp.IntEq_trans xy.right.right.left yz.right.right.left,
        BEDC.Derived.RationalUp.IntEq_trans xy.right.right.right.left
          yz.right.right.right.left,
        BEDC.Derived.RationalUp.IntEq_trans xy.right.right.right.right
          yz.right.right.right.right⟩

def ResolventPackage.rel (x y : ResolventPackage) : Prop :=
  QuarticCoefficients.rel x.coefficients y.coefficients ∧
    BEDC.Derived.PolynomialUp.PolyEq x.polynomial y.polynomial

def ResolventPackage.admissible (x : ResolventPackage) : Prop :=
  BEDC.Derived.PolynomialUp.PolyEq x.polynomial (resolventPoly x.coefficients)

def ResolventPackage.observations (x : ResolventPackage) : List BHist :=
  QuarticCoefficients.observations x.coefficients ++
    [signedMagnitudeObservation (resolventR x.coefficients),
      signedMagnitudeObservation (resolventQ x.coefficients),
      signedMagnitudeObservation (resolventP x.coefficients)]

def ResolventPackageRelEquiv : RelEquiv ResolventPackage where
  rel := ResolventPackage.rel
  refl := by
    intro x
    exact
      ⟨QuarticCoefficientsRelEquiv.refl x.coefficients,
        BEDC.Derived.PolynomialUp.PolyEq_refl x.polynomial⟩
  symm := by
    intro x y same
    exact
      ⟨QuarticCoefficientsRelEquiv.symm same.left,
        BEDC.Derived.PolynomialUp.PolyEq_symm same.right⟩
  trans := by
    intro x y z xy yz
    exact
      ⟨QuarticCoefficientsRelEquiv.trans xy.left yz.left,
        BEDC.Derived.PolynomialUp.PolyEq_trans xy.right yz.right⟩

def CompanionPackage.rel (x y : CompanionPackage) : Prop :=
  QuarticCoefficients.rel x.coefficients y.coefficients ∧
    BEDC.Derived.MatrixUp.MatEq x.topBlock y.topBlock ∧
      BEDC.Derived.MatrixUp.MatEq x.bottomBlock y.bottomBlock

def CompanionPackage.admissible (x : CompanionPackage) : Prop :=
  BEDC.Derived.MatrixUp.MatEq x.topBlock (companionBlockTop x.coefficients) ∧
    BEDC.Derived.MatrixUp.MatEq x.bottomBlock (companionBlockBottom x.coefficients)

def mat2Observations (m : BEDC.Derived.MatrixUp.Mat2) : List BHist :=
  [signedMagnitudeObservation m.a00, signedMagnitudeObservation m.a01,
    signedMagnitudeObservation m.a10, signedMagnitudeObservation m.a11]

def CompanionPackage.observations (x : CompanionPackage) : List BHist :=
  QuarticCoefficients.observations x.coefficients ++
    mat2Observations x.topBlock ++ mat2Observations x.bottomBlock

def CompanionPackageRelEquiv : RelEquiv CompanionPackage where
  rel := CompanionPackage.rel
  refl := by
    intro x
    exact
      ⟨QuarticCoefficientsRelEquiv.refl x.coefficients,
        BEDC.Derived.MatrixUp.MatEq_refl x.topBlock,
        BEDC.Derived.MatrixUp.MatEq_refl x.bottomBlock⟩
  symm := by
    intro x y same
    exact
      ⟨QuarticCoefficientsRelEquiv.symm same.left,
        BEDC.Derived.MatrixUp.MatEq_symm same.right.left,
        BEDC.Derived.MatrixUp.MatEq_symm same.right.right⟩
  trans := by
    intro x y z xy yz
    exact
      ⟨QuarticCoefficientsRelEquiv.trans xy.left yz.left,
        BEDC.Derived.MatrixUp.MatEq_trans xy.right.left yz.right.left,
        BEDC.Derived.MatrixUp.MatEq_trans xy.right.right yz.right.right⟩

def SpectralTarget : SpectralProjection -> Type
  | SpectralProjection.resolvent => ResolventPackage
  | SpectralProjection.companion => CompanionPackage

def spectralTargetInterface : (i : SpectralProjection) -> RealityInterface
  | SpectralProjection.resolvent =>
      { Carrier := ResolventPackage
        classifier := ResolventPackageRelEquiv
        admissible := ResolventPackage.admissible
        observations := ResolventPackage.observations
        ledger := fun _ => emptyProjectionLedger }
  | SpectralProjection.companion =>
      { Carrier := CompanionPackage
        classifier := CompanionPackageRelEquiv
        admissible := CompanionPackage.admissible
        observations := CompanionPackage.observations
        ledger := fun _ => emptyProjectionLedger }

def spectralProject :
    (i : SpectralProjection) -> QuarticCoefficients ->
      (spectralTargetInterface i).Carrier
  | SpectralProjection.resolvent, q => resolventPackage q
  | SpectralProjection.companion, q => companionPackage q

def quarticProjectionLedger (_i : SpectralProjection) (_q : QuarticCoefficients) :
    ProjectionLedger :=
  emptyProjectionLedger

def QuarticSpectralSource : RealityInterface :=
  { Carrier := QuarticCoefficients
    classifier := QuarticCoefficientsRelEquiv
    admissible := QuarticCoefficients.admissible
    observations := QuarticCoefficients.observations
    ledger := fun _ => emptyProjectionLedger }

theorem quartic_poly_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y -> BEDC.Derived.PolynomialUp.PolyEq (QuarticCoefficients.poly x)
      (QuarticCoefficients.poly y) := by
  intro same n
  cases n with
  | zero =>
      exact same.left
  | succ n =>
      cases n with
      | zero =>
          exact same.right.left
      | succ n =>
          cases n with
          | zero =>
              exact same.right.right.left
          | succ n =>
              cases n with
              | zero =>
                  exact same.right.right.right.left
              | succ n =>
                  cases n with
                  | zero =>
                      exact same.right.right.right.right
                  | succ _ =>
                      exact BEDC.Derived.RationalUp.IntEq_refl izero

theorem resolventP_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y -> ieq (resolventP x) (resolventP y) := by
  intro same
  exact BEDC.Derived.IntUp.IntAdd_respects
    (BEDC.Derived.IntUp.IntMul_respects (BEDC.Derived.RationalUp.IntEq_refl ieight) same.right.right.left)
    (BEDC.Derived.IntUp.IntNeg_respects
      (BEDC.Derived.IntUp.IntMul_respects (BEDC.Derived.RationalUp.IntEq_refl ithree)
        (BEDC.Derived.IntUp.IntMul_respects same.right.right.right.left
          same.right.right.right.left)))

theorem resolventQ_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y -> ieq (resolventQ x) (resolventQ y) := by
  intro same
  have cubeSame :
      ieq (icube x.c3) (icube y.c3) :=
    BEDC.Derived.IntUp.IntMul_respects
      (BEDC.Derived.IntUp.IntMul_respects same.right.right.right.left same.right.right.right.left)
      same.right.right.right.left
  have linearSame :
      ieq (imul ieight x.c1) (imul ieight y.c1) :=
    BEDC.Derived.IntUp.IntMul_respects (BEDC.Derived.RationalUp.IntEq_refl ieight) same.right.left
  have mixedSame :
      ieq (imul ifour (imul x.c3 x.c2)) (imul ifour (imul y.c3 y.c2)) :=
    BEDC.Derived.IntUp.IntMul_respects (BEDC.Derived.RationalUp.IntEq_refl ifour)
      (BEDC.Derived.IntUp.IntMul_respects same.right.right.right.left same.right.right.left)
  exact BEDC.Derived.IntUp.IntAdd_respects cubeSame
    (BEDC.Derived.IntUp.IntAdd_respects linearSame (BEDC.Derived.IntUp.IntNeg_respects mixedSame))

theorem resolventR_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y -> ieq (resolventR x) (resolventR y) := by
  intro same
  have quadraticSame :
      ieq (imul (isquare x.c3) x.c2) (imul (isquare y.c3) y.c2) :=
    BEDC.Derived.IntUp.IntMul_respects
      (BEDC.Derived.IntUp.IntMul_respects same.right.right.right.left same.right.right.right.left)
      same.right.right.left
  have constantSame :
      ieq (imul ifour x.c0) (imul ifour y.c0) :=
    BEDC.Derived.IntUp.IntMul_respects (BEDC.Derived.RationalUp.IntEq_refl ifour) same.left
  have mixedSame :
      ieq (imul x.c3 x.c1) (imul y.c3 y.c1) :=
    BEDC.Derived.IntUp.IntMul_respects same.right.right.right.left same.right.left
  exact BEDC.Derived.IntUp.IntAdd_respects quadraticSame
    (BEDC.Derived.IntUp.IntAdd_respects (BEDC.Derived.IntUp.IntNeg_respects constantSame)
      (BEDC.Derived.IntUp.IntNeg_respects mixedSame))

theorem resolventPoly_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y -> BEDC.Derived.PolynomialUp.PolyEq (resolventPoly x) (resolventPoly y) := by
  intro same n
  cases n with
  | zero =>
      exact resolventR_respects same
  | succ n =>
      cases n with
      | zero =>
          exact resolventQ_respects same
      | succ n =>
          cases n with
          | zero =>
              exact resolventP_respects same
          | succ n =>
              cases n with
              | zero =>
                  exact BEDC.Derived.RationalUp.IntEq_refl ione
              | succ _ =>
                  exact BEDC.Derived.RationalUp.IntEq_refl izero

theorem companionBlockTop_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y -> BEDC.Derived.MatrixUp.MatEq (companionBlockTop x) (companionBlockTop y) := by
  intro _same
  unfold companionBlockTop BEDC.Derived.MatrixUp.MatEq
  exact
    ⟨BEDC.Derived.RationalUp.IntEq_refl izero, BEDC.Derived.RationalUp.IntEq_refl ione,
      BEDC.Derived.RationalUp.IntEq_refl izero, BEDC.Derived.RationalUp.IntEq_refl izero⟩

theorem companionBlockBottom_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y -> BEDC.Derived.MatrixUp.MatEq (companionBlockBottom x)
      (companionBlockBottom y) := by
  intro same
  unfold companionBlockBottom BEDC.Derived.MatrixUp.MatEq
  exact
    ⟨BEDC.Derived.IntUp.IntNeg_respects same.left,
      BEDC.Derived.IntUp.IntNeg_respects same.right.left,
      BEDC.Derived.RationalUp.IntEq_refl ione,
      BEDC.Derived.IntUp.IntNeg_respects same.right.right.left⟩

theorem resolventPackage_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y ->
      ResolventPackage.rel (resolventPackage x) (resolventPackage y) := by
  intro same
  exact ⟨same, resolventPoly_respects same⟩

theorem companionPackage_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y ->
      CompanionPackage.rel (companionPackage x) (companionPackage y) := by
  intro same
  exact
    ⟨same, companionBlockTop_respects same, companionBlockBottom_respects same⟩

def QuarticSpectralCommonCarrier : CommonCarrier SpectralProjection :=
  { source := QuarticSpectralSource
    target := spectralTargetInterface
    project := spectralProject
    project_respects := by
      intro i x y same
      cases i
      · exact resolventPackage_respects same
      · exact companionPackage_respects same
    projectionLedger := quarticProjectionLedger }

theorem QuarticSpectralCommonCarrier_resolvent_projection {q : QuarticCoefficients} :
    QuarticSpectralCommonCarrier.project SpectralProjection.resolvent q =
      resolventPackage q := by
  rfl

theorem QuarticSpectralCommonCarrier_companion_projection {q : QuarticCoefficients} :
    QuarticSpectralCommonCarrier.project SpectralProjection.companion q =
      companionPackage q := by
  rfl

theorem QuarticSpectralCommonCarrier_resolvent_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y ->
      ResolventPackage.rel
        (QuarticSpectralCommonCarrier.project SpectralProjection.resolvent x)
        (QuarticSpectralCommonCarrier.project SpectralProjection.resolvent y) := by
  intro same
  exact BEDC.Derived.CommonCarrierProjectionUp.projection_preserves_classified_identity
    QuarticSpectralCommonCarrier SpectralProjection.resolvent same

theorem QuarticSpectralCommonCarrier_companion_respects {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y ->
      CompanionPackage.rel
        (QuarticSpectralCommonCarrier.project SpectralProjection.companion x)
        (QuarticSpectralCommonCarrier.project SpectralProjection.companion y) := by
  intro same
  exact BEDC.Derived.CommonCarrierProjectionUp.projection_preserves_classified_identity
    QuarticSpectralCommonCarrier SpectralProjection.companion same

theorem QuarticSpectralCommonCarrier_connection {x y : QuarticCoefficients} :
    QuarticCoefficients.rel x y ->
      BEDC.Derived.PolynomialUp.PolyEq (QuarticCoefficients.poly x) (QuarticCoefficients.poly y) ∧
        ResolventPackage.rel
          (QuarticSpectralCommonCarrier.project SpectralProjection.resolvent x)
          (QuarticSpectralCommonCarrier.project SpectralProjection.resolvent y) ∧
        CompanionPackage.rel
          (QuarticSpectralCommonCarrier.project SpectralProjection.companion x)
          (QuarticSpectralCommonCarrier.project SpectralProjection.companion y) := by
  intro same
  exact
    ⟨quartic_poly_respects same,
      QuarticSpectralCommonCarrier_resolvent_respects same,
      QuarticSpectralCommonCarrier_companion_respects same⟩

def fixedQuarticConstant (y : IntegerUp) : IntegerUp :=
  iadd (isquare y) y

def fixedQuarticMiddle (y : IntegerUp) : IntegerUp :=
  ineg (iadd (imul itwo y) ione)

def fixedQuarticCoefficients (y : IntegerUp) : QuarticCoefficients :=
  { c0 := fixedQuarticConstant y
    c1 := ione
    c2 := fixedQuarticMiddle y
    c3 := ineg ione
    c4 := ione }

def fixedQuarticSpectralPolynomial (y : IntegerUp) : Poly :=
  QuarticCoefficients.poly (fixedQuarticCoefficients y)

def fixedRecurrenceNumerator (y : IntegerUp) : Poly :=
  [ione, y, isub (isub (isquare y) y) ione,
    isub (icube y) (imul itwo y)]

def fixedRecurrenceDenominator (y : IntegerUp) : Poly :=
  [ione, ineg ione, fixedQuarticMiddle y, ione, fixedQuarticConstant y]

def reciprocalQuarticFace (p : Poly) : Poly :=
  [BEDC.Derived.PolynomialUp.polyCoeff p 4,
    BEDC.Derived.PolynomialUp.polyCoeff p 3,
    BEDC.Derived.PolynomialUp.polyCoeff p 2,
    BEDC.Derived.PolynomialUp.polyCoeff p 1,
    BEDC.Derived.PolynomialUp.polyCoeff p 0]

theorem fixedQuarticCoefficients_respects {y z : IntegerUp} :
    ieq y z -> QuarticCoefficients.rel (fixedQuarticCoefficients y)
      (fixedQuarticCoefficients z) := by
  intro same
  have constantSame :
      ieq (fixedQuarticConstant y) (fixedQuarticConstant z) :=
    BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntMul_respects same same) same
  have middleInnerSame :
      ieq (iadd (imul itwo y) ione) (iadd (imul itwo z) ione) :=
    BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntMul_respects
        (BEDC.Derived.RationalUp.IntEq_refl itwo) same)
      (BEDC.Derived.RationalUp.IntEq_refl ione)
  exact
    ⟨constantSame,
      BEDC.Derived.RationalUp.IntEq_refl ione,
      BEDC.Derived.IntUp.IntNeg_respects middleInnerSame,
      BEDC.Derived.RationalUp.IntEq_refl (ineg ione),
      BEDC.Derived.RationalUp.IntEq_refl ione⟩

theorem fixedQuarticSpectralPolynomial_respects {y z : IntegerUp} :
    ieq y z -> BEDC.Derived.PolynomialUp.PolyEq
      (fixedQuarticSpectralPolynomial y) (fixedQuarticSpectralPolynomial z) := by
  intro same
  exact quartic_poly_respects (fixedQuarticCoefficients_respects same)

theorem fixedRecurrenceNumerator_respects {y z : IntegerUp} :
    ieq y z -> BEDC.Derived.PolynomialUp.PolyEq
      (fixedRecurrenceNumerator y) (fixedRecurrenceNumerator z) := by
  intro same n
  have squareSame : ieq (isquare y) (isquare z) :=
    BEDC.Derived.IntUp.IntMul_respects same same
  have cubeSame : ieq (icube y) (icube z) :=
    BEDC.Derived.IntUp.IntMul_respects squareSame same
  cases n with
  | zero =>
      exact BEDC.Derived.RationalUp.IntEq_refl ione
  | succ n =>
      cases n with
      | zero =>
          exact same
      | succ n =>
          cases n with
          | zero =>
              exact BEDC.Derived.IntUp.IntAdd_respects
                (BEDC.Derived.IntUp.IntAdd_respects squareSame
                  (BEDC.Derived.IntUp.IntNeg_respects same))
                (BEDC.Derived.RationalUp.IntEq_refl (ineg ione))
          | succ n =>
              cases n with
              | zero =>
                  exact BEDC.Derived.IntUp.IntAdd_respects cubeSame
                    (BEDC.Derived.IntUp.IntNeg_respects
                      (BEDC.Derived.IntUp.IntMul_respects
                        (BEDC.Derived.RationalUp.IntEq_refl itwo) same))
              | succ _ =>
                  exact BEDC.Derived.RationalUp.IntEq_refl izero

theorem fixedRecurrenceDenominator_respects {y z : IntegerUp} :
    ieq y z -> BEDC.Derived.PolynomialUp.PolyEq
      (fixedRecurrenceDenominator y) (fixedRecurrenceDenominator z) := by
  intro same n
  have coeffSame := fixedQuarticCoefficients_respects same
  cases n with
  | zero =>
      exact BEDC.Derived.RationalUp.IntEq_refl ione
  | succ n =>
      cases n with
      | zero =>
          exact BEDC.Derived.RationalUp.IntEq_refl (ineg ione)
      | succ n =>
          cases n with
          | zero =>
              exact coeffSame.right.right.left
          | succ n =>
              cases n with
              | zero =>
                  exact BEDC.Derived.RationalUp.IntEq_refl ione
              | succ n =>
                  cases n with
                  | zero =>
                      exact coeffSame.left
                  | succ _ =>
                      exact BEDC.Derived.RationalUp.IntEq_refl izero

theorem reciprocalQuarticFace_respects {p q : Poly} :
    BEDC.Derived.PolynomialUp.PolyEq p q ->
      BEDC.Derived.PolynomialUp.PolyEq (reciprocalQuarticFace p)
        (reciprocalQuarticFace q) := by
  intro same n
  cases n with
  | zero =>
      exact same 4
  | succ n =>
      cases n with
      | zero =>
          exact same 3
      | succ n =>
          cases n with
          | zero =>
              exact same 2
          | succ n =>
              cases n with
              | zero =>
                  exact same 1
              | succ n =>
                  cases n with
                  | zero =>
                      exact same 0
                  | succ _ =>
                      exact BEDC.Derived.RationalUp.IntEq_refl izero

theorem fixedQuartic_reciprocal_face_matches_spectral {y : IntegerUp} :
    BEDC.Derived.PolynomialUp.PolyEq
      (reciprocalQuarticFace (fixedRecurrenceDenominator y))
      (fixedQuarticSpectralPolynomial y) := by
  intro n
  cases n with
  | zero =>
      exact BEDC.Derived.RationalUp.IntEq_refl (fixedQuarticConstant y)
  | succ n =>
      cases n with
      | zero =>
          exact BEDC.Derived.RationalUp.IntEq_refl ione
      | succ n =>
          cases n with
          | zero =>
              exact BEDC.Derived.RationalUp.IntEq_refl (fixedQuarticMiddle y)
          | succ n =>
              cases n with
              | zero =>
                  exact BEDC.Derived.RationalUp.IntEq_refl (ineg ione)
              | succ n =>
                  cases n with
                  | zero =>
                      exact BEDC.Derived.RationalUp.IntEq_refl ione
                  | succ _ =>
                      exact BEDC.Derived.RationalUp.IntEq_refl izero

structure FixedQuarticCarrier where
  parameter : IntegerUp

def FixedQuarticCarrier.rel (x y : FixedQuarticCarrier) : Prop :=
  ieq x.parameter y.parameter

def FixedQuarticCarrier.observations (x : FixedQuarticCarrier) : List BHist :=
  [signedMagnitudeObservation x.parameter] ++
    QuarticCoefficients.observations (fixedQuarticCoefficients x.parameter)

def FixedQuarticCarrier.admissible (x : FixedQuarticCarrier) : Prop :=
  BEDC.Derived.PolynomialUp.PolyEq
    (reciprocalQuarticFace (fixedRecurrenceDenominator x.parameter))
    (fixedQuarticSpectralPolynomial x.parameter)

def FixedQuarticCarrierRelEquiv : RelEquiv FixedQuarticCarrier where
  rel := FixedQuarticCarrier.rel
  refl := by
    intro x
    exact BEDC.Derived.RationalUp.IntEq_refl x.parameter
  symm := by
    intro x y same
    exact BEDC.Derived.RationalUp.IntEq_symm same
  trans := by
    intro x y z xy yz
    exact BEDC.Derived.RationalUp.IntEq_trans xy yz

structure RecurrencePackage where
  parameter : IntegerUp
  numerator : Poly
  denominator : Poly
  spectralFace : Poly

def recurrencePackage (y : IntegerUp) : RecurrencePackage :=
  { parameter := y
    numerator := fixedRecurrenceNumerator y
    denominator := fixedRecurrenceDenominator y
    spectralFace := reciprocalQuarticFace (fixedRecurrenceDenominator y) }

def RecurrencePackage.rel (x y : RecurrencePackage) : Prop :=
  ieq x.parameter y.parameter ∧
    BEDC.Derived.PolynomialUp.PolyEq x.numerator y.numerator ∧
      BEDC.Derived.PolynomialUp.PolyEq x.denominator y.denominator ∧
        BEDC.Derived.PolynomialUp.PolyEq x.spectralFace y.spectralFace

def RecurrencePackage.admissible (x : RecurrencePackage) : Prop :=
  BEDC.Derived.PolynomialUp.PolyEq x.numerator
      (fixedRecurrenceNumerator x.parameter) ∧
    BEDC.Derived.PolynomialUp.PolyEq x.denominator
      (fixedRecurrenceDenominator x.parameter) ∧
    BEDC.Derived.PolynomialUp.PolyEq x.spectralFace
      (fixedQuarticSpectralPolynomial x.parameter)

def RecurrencePackage.observations (x : RecurrencePackage) : List BHist :=
  [signedMagnitudeObservation x.parameter] ++
    QuarticCoefficients.observations (fixedQuarticCoefficients x.parameter)

def RecurrencePackageRelEquiv : RelEquiv RecurrencePackage where
  rel := RecurrencePackage.rel
  refl := by
    intro x
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_refl x.parameter,
        BEDC.Derived.PolynomialUp.PolyEq_refl x.numerator,
        BEDC.Derived.PolynomialUp.PolyEq_refl x.denominator,
        BEDC.Derived.PolynomialUp.PolyEq_refl x.spectralFace⟩
  symm := by
    intro x y same
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_symm same.left,
        BEDC.Derived.PolynomialUp.PolyEq_symm same.right.left,
        BEDC.Derived.PolynomialUp.PolyEq_symm same.right.right.left,
        BEDC.Derived.PolynomialUp.PolyEq_symm same.right.right.right⟩
  trans := by
    intro x y z xy yz
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_trans xy.left yz.left,
        BEDC.Derived.PolynomialUp.PolyEq_trans xy.right.left yz.right.left,
        BEDC.Derived.PolynomialUp.PolyEq_trans xy.right.right.left yz.right.right.left,
        BEDC.Derived.PolynomialUp.PolyEq_trans xy.right.right.right
          yz.right.right.right⟩

def fixedCompanionBlock00 (y : IntegerUp) : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := ione
    a01 := iadd (imul itwo y) ione
    a10 := ione
    a11 := izero }

def fixedCompanionBlock01 (y : IntegerUp) : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := ineg ione
    a01 := ineg (fixedQuarticConstant y)
    a10 := izero
    a11 := izero }

def fixedCompanionBlock10 (_ : IntegerUp) : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := izero
    a01 := ione
    a10 := izero
    a11 := izero }

def fixedCompanionBlock11 (_ : IntegerUp) : BEDC.Derived.MatrixUp.Mat2 :=
  { a00 := izero
    a01 := izero
    a10 := ione
    a11 := izero }

structure CompanionSpectrumPackage where
  parameter : IntegerUp
  block00 : BEDC.Derived.MatrixUp.Mat2
  block01 : BEDC.Derived.MatrixUp.Mat2
  block10 : BEDC.Derived.MatrixUp.Mat2
  block11 : BEDC.Derived.MatrixUp.Mat2
  spectralPolynomial : Poly

def companionSpectrumPackage (y : IntegerUp) : CompanionSpectrumPackage :=
  { parameter := y
    block00 := fixedCompanionBlock00 y
    block01 := fixedCompanionBlock01 y
    block10 := fixedCompanionBlock10 y
    block11 := fixedCompanionBlock11 y
    spectralPolynomial := fixedQuarticSpectralPolynomial y }

def CompanionSpectrumPackage.rel (x y : CompanionSpectrumPackage) : Prop :=
  ieq x.parameter y.parameter ∧
    BEDC.Derived.MatrixUp.MatEq x.block00 y.block00 ∧
      BEDC.Derived.MatrixUp.MatEq x.block01 y.block01 ∧
        BEDC.Derived.MatrixUp.MatEq x.block10 y.block10 ∧
          BEDC.Derived.MatrixUp.MatEq x.block11 y.block11 ∧
            BEDC.Derived.PolynomialUp.PolyEq x.spectralPolynomial y.spectralPolynomial

def CompanionSpectrumPackage.admissible (x : CompanionSpectrumPackage) : Prop :=
  BEDC.Derived.MatrixUp.MatEq x.block00 (fixedCompanionBlock00 x.parameter) ∧
    BEDC.Derived.MatrixUp.MatEq x.block01 (fixedCompanionBlock01 x.parameter) ∧
      BEDC.Derived.MatrixUp.MatEq x.block10 (fixedCompanionBlock10 x.parameter) ∧
        BEDC.Derived.MatrixUp.MatEq x.block11 (fixedCompanionBlock11 x.parameter) ∧
          BEDC.Derived.PolynomialUp.PolyEq x.spectralPolynomial
            (fixedQuarticSpectralPolynomial x.parameter)

def CompanionSpectrumPackage.observations (x : CompanionSpectrumPackage) : List BHist :=
  [signedMagnitudeObservation x.parameter] ++
    mat2Observations x.block00 ++ mat2Observations x.block01 ++
      mat2Observations x.block10 ++ mat2Observations x.block11

def CompanionSpectrumPackageRelEquiv : RelEquiv CompanionSpectrumPackage where
  rel := CompanionSpectrumPackage.rel
  refl := by
    intro x
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_refl x.parameter,
        BEDC.Derived.MatrixUp.MatEq_refl x.block00,
        BEDC.Derived.MatrixUp.MatEq_refl x.block01,
        BEDC.Derived.MatrixUp.MatEq_refl x.block10,
        BEDC.Derived.MatrixUp.MatEq_refl x.block11,
        BEDC.Derived.PolynomialUp.PolyEq_refl x.spectralPolynomial⟩
  symm := by
    intro x y same
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_symm same.left,
        BEDC.Derived.MatrixUp.MatEq_symm same.right.left,
        BEDC.Derived.MatrixUp.MatEq_symm same.right.right.left,
        BEDC.Derived.MatrixUp.MatEq_symm same.right.right.right.left,
        BEDC.Derived.MatrixUp.MatEq_symm same.right.right.right.right.left,
        BEDC.Derived.PolynomialUp.PolyEq_symm same.right.right.right.right.right⟩
  trans := by
    intro x y z xy yz
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_trans xy.left yz.left,
        BEDC.Derived.MatrixUp.MatEq_trans xy.right.left yz.right.left,
        BEDC.Derived.MatrixUp.MatEq_trans xy.right.right.left yz.right.right.left,
        BEDC.Derived.MatrixUp.MatEq_trans xy.right.right.right.left
          yz.right.right.right.left,
        BEDC.Derived.MatrixUp.MatEq_trans xy.right.right.right.right.left
          yz.right.right.right.right.left,
        BEDC.Derived.PolynomialUp.PolyEq_trans xy.right.right.right.right.right
          yz.right.right.right.right.right⟩

theorem fixedCompanionBlock00_respects {y z : IntegerUp} :
    ieq y z -> BEDC.Derived.MatrixUp.MatEq
      (fixedCompanionBlock00 y) (fixedCompanionBlock00 z) := by
  intro same
  unfold fixedCompanionBlock00 BEDC.Derived.MatrixUp.MatEq
  exact
    ⟨BEDC.Derived.RationalUp.IntEq_refl ione,
      BEDC.Derived.IntUp.IntAdd_respects
        (BEDC.Derived.IntUp.IntMul_respects
          (BEDC.Derived.RationalUp.IntEq_refl itwo) same)
        (BEDC.Derived.RationalUp.IntEq_refl ione),
      BEDC.Derived.RationalUp.IntEq_refl ione,
      BEDC.Derived.RationalUp.IntEq_refl izero⟩

theorem fixedCompanionBlock01_respects {y z : IntegerUp} :
    ieq y z -> BEDC.Derived.MatrixUp.MatEq
      (fixedCompanionBlock01 y) (fixedCompanionBlock01 z) := by
  intro same
  have constantSame :
      ieq (fixedQuarticConstant y) (fixedQuarticConstant z) :=
    BEDC.Derived.IntUp.IntAdd_respects
      (BEDC.Derived.IntUp.IntMul_respects same same) same
  unfold fixedCompanionBlock01 BEDC.Derived.MatrixUp.MatEq
  exact
    ⟨BEDC.Derived.RationalUp.IntEq_refl (ineg ione),
      BEDC.Derived.IntUp.IntNeg_respects constantSame,
      BEDC.Derived.RationalUp.IntEq_refl izero,
      BEDC.Derived.RationalUp.IntEq_refl izero⟩

theorem fixedCompanionBlock10_respects {y z : IntegerUp} :
    ieq y z -> BEDC.Derived.MatrixUp.MatEq
      (fixedCompanionBlock10 y) (fixedCompanionBlock10 z) := by
  intro _same
  unfold fixedCompanionBlock10 BEDC.Derived.MatrixUp.MatEq
  exact
    ⟨BEDC.Derived.RationalUp.IntEq_refl izero,
      BEDC.Derived.RationalUp.IntEq_refl ione,
      BEDC.Derived.RationalUp.IntEq_refl izero,
      BEDC.Derived.RationalUp.IntEq_refl izero⟩

theorem fixedCompanionBlock11_respects {y z : IntegerUp} :
    ieq y z -> BEDC.Derived.MatrixUp.MatEq
      (fixedCompanionBlock11 y) (fixedCompanionBlock11 z) := by
  intro _same
  unfold fixedCompanionBlock11 BEDC.Derived.MatrixUp.MatEq
  exact
    ⟨BEDC.Derived.RationalUp.IntEq_refl izero,
      BEDC.Derived.RationalUp.IntEq_refl izero,
      BEDC.Derived.RationalUp.IntEq_refl ione,
      BEDC.Derived.RationalUp.IntEq_refl izero⟩

theorem companionSpectrumPackage_respects {y z : IntegerUp} :
    ieq y z -> CompanionSpectrumPackage.rel
      (companionSpectrumPackage y) (companionSpectrumPackage z) := by
  intro same
  exact
    ⟨same, fixedCompanionBlock00_respects same, fixedCompanionBlock01_respects same,
      fixedCompanionBlock10_respects same, fixedCompanionBlock11_respects same,
      fixedQuarticSpectralPolynomial_respects same⟩

structure BalancedQuarticRows where
  a : IntegerUp
  c : IntegerUp
  d : IntegerUp
  g : IntegerUp

def canonicalBalancedQuarticRows : BalancedQuarticRows :=
  { a := ineg ione
    c := ineg ione
    d := ione
    g := izero }

def BalancedQuarticRows.rel (x y : BalancedQuarticRows) : Prop :=
  ieq x.a y.a ∧ ieq x.c y.c ∧ ieq x.d y.d ∧ ieq x.g y.g

def canonicalWeierstrassCubic : Poly :=
  [ione, ineg ifour, izero, ifour]

structure AlgebraGeometryPackage where
  parameter : IntegerUp
  spectralCoefficients : QuarticCoefficients
  balancedRows : BalancedQuarticRows
  weierstrassCubic : Poly

def algebraGeometryPackage (y : IntegerUp) : AlgebraGeometryPackage :=
  { parameter := y
    spectralCoefficients := fixedQuarticCoefficients y
    balancedRows := canonicalBalancedQuarticRows
    weierstrassCubic := canonicalWeierstrassCubic }

def AlgebraGeometryPackage.rel (x y : AlgebraGeometryPackage) : Prop :=
  ieq x.parameter y.parameter ∧
    QuarticCoefficients.rel x.spectralCoefficients y.spectralCoefficients ∧
      BalancedQuarticRows.rel x.balancedRows y.balancedRows ∧
        BEDC.Derived.PolynomialUp.PolyEq x.weierstrassCubic y.weierstrassCubic

def AlgebraGeometryPackage.admissible (x : AlgebraGeometryPackage) : Prop :=
  QuarticCoefficients.rel x.spectralCoefficients (fixedQuarticCoefficients x.parameter) ∧
    BalancedQuarticRows.rel x.balancedRows canonicalBalancedQuarticRows ∧
      BEDC.Derived.PolynomialUp.PolyEq x.weierstrassCubic canonicalWeierstrassCubic

def balancedRowsObservations (x : BalancedQuarticRows) : List BHist :=
  [signedMagnitudeObservation x.a, signedMagnitudeObservation x.c,
    signedMagnitudeObservation x.d, signedMagnitudeObservation x.g]

def AlgebraGeometryPackage.observations (x : AlgebraGeometryPackage) : List BHist :=
  [signedMagnitudeObservation x.parameter] ++
    QuarticCoefficients.observations x.spectralCoefficients ++
      balancedRowsObservations x.balancedRows

def BalancedQuarticRows_rel_refl (x : BalancedQuarticRows) :
    BalancedQuarticRows.rel x x :=
  ⟨BEDC.Derived.RationalUp.IntEq_refl x.a,
    BEDC.Derived.RationalUp.IntEq_refl x.c,
    BEDC.Derived.RationalUp.IntEq_refl x.d,
    BEDC.Derived.RationalUp.IntEq_refl x.g⟩

theorem BalancedQuarticRows_rel_symm {x y : BalancedQuarticRows} :
    BalancedQuarticRows.rel x y -> BalancedQuarticRows.rel y x := by
  intro same
  exact
    ⟨BEDC.Derived.RationalUp.IntEq_symm same.left,
      BEDC.Derived.RationalUp.IntEq_symm same.right.left,
      BEDC.Derived.RationalUp.IntEq_symm same.right.right.left,
      BEDC.Derived.RationalUp.IntEq_symm same.right.right.right⟩

theorem BalancedQuarticRows_rel_trans {x y z : BalancedQuarticRows} :
    BalancedQuarticRows.rel x y -> BalancedQuarticRows.rel y z ->
      BalancedQuarticRows.rel x z := by
  intro xy yz
  exact
    ⟨BEDC.Derived.RationalUp.IntEq_trans xy.left yz.left,
      BEDC.Derived.RationalUp.IntEq_trans xy.right.left yz.right.left,
      BEDC.Derived.RationalUp.IntEq_trans xy.right.right.left yz.right.right.left,
      BEDC.Derived.RationalUp.IntEq_trans xy.right.right.right yz.right.right.right⟩

def AlgebraGeometryPackageRelEquiv : RelEquiv AlgebraGeometryPackage where
  rel := AlgebraGeometryPackage.rel
  refl := by
    intro x
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_refl x.parameter,
        QuarticCoefficientsRelEquiv.refl x.spectralCoefficients,
        BalancedQuarticRows_rel_refl x.balancedRows,
        BEDC.Derived.PolynomialUp.PolyEq_refl x.weierstrassCubic⟩
  symm := by
    intro x y same
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_symm same.left,
        QuarticCoefficientsRelEquiv.symm same.right.left,
        BalancedQuarticRows_rel_symm same.right.right.left,
        BEDC.Derived.PolynomialUp.PolyEq_symm same.right.right.right⟩
  trans := by
    intro x y z xy yz
    exact
      ⟨BEDC.Derived.RationalUp.IntEq_trans xy.left yz.left,
        QuarticCoefficientsRelEquiv.trans xy.right.left yz.right.left,
        BalancedQuarticRows_rel_trans xy.right.right.left yz.right.right.left,
        BEDC.Derived.PolynomialUp.PolyEq_trans xy.right.right.right
          yz.right.right.right⟩

theorem algebraGeometryPackage_respects {y z : IntegerUp} :
    ieq y z -> AlgebraGeometryPackage.rel
      (algebraGeometryPackage y) (algebraGeometryPackage z) := by
  intro same
  exact
    ⟨same, fixedQuarticCoefficients_respects same,
      BalancedQuarticRows_rel_refl canonicalBalancedQuarticRows,
      BEDC.Derived.PolynomialUp.PolyEq_refl canonicalWeierstrassCubic⟩

theorem recurrencePackage_respects {y z : IntegerUp} :
    ieq y z -> RecurrencePackage.rel (recurrencePackage y) (recurrencePackage z) := by
  intro same
  exact
    ⟨same, fixedRecurrenceNumerator_respects same,
      fixedRecurrenceDenominator_respects same,
      reciprocalQuarticFace_respects (fixedRecurrenceDenominator_respects same)⟩

theorem resolventPackage_fixed_respects {y z : IntegerUp} :
    ieq y z -> ResolventPackage.rel
      (resolventPackage (fixedQuarticCoefficients y))
      (resolventPackage (fixedQuarticCoefficients z)) := by
  intro same
  exact resolventPackage_respects (fixedQuarticCoefficients_respects same)

inductive FixedCarrierProjection where
  | recurrence
  | resolvent
  | companion
  | algebraGeometry

def fixedTargetInterface : (i : FixedCarrierProjection) -> RealityInterface
  | FixedCarrierProjection.recurrence =>
      { Carrier := RecurrencePackage
        classifier := RecurrencePackageRelEquiv
        admissible := RecurrencePackage.admissible
        observations := RecurrencePackage.observations
        ledger := fun _ => emptyProjectionLedger }
  | FixedCarrierProjection.resolvent =>
      { Carrier := ResolventPackage
        classifier := ResolventPackageRelEquiv
        admissible := ResolventPackage.admissible
        observations := ResolventPackage.observations
        ledger := fun _ => emptyProjectionLedger }
  | FixedCarrierProjection.companion =>
      { Carrier := CompanionSpectrumPackage
        classifier := CompanionSpectrumPackageRelEquiv
        admissible := CompanionSpectrumPackage.admissible
        observations := CompanionSpectrumPackage.observations
        ledger := fun _ => emptyProjectionLedger }
  | FixedCarrierProjection.algebraGeometry =>
      { Carrier := AlgebraGeometryPackage
        classifier := AlgebraGeometryPackageRelEquiv
        admissible := AlgebraGeometryPackage.admissible
        observations := AlgebraGeometryPackage.observations
        ledger := fun _ => emptyProjectionLedger }

def fixedProject :
    (i : FixedCarrierProjection) -> FixedQuarticCarrier ->
      (fixedTargetInterface i).Carrier
  | FixedCarrierProjection.recurrence, x => recurrencePackage x.parameter
  | FixedCarrierProjection.resolvent, x => resolventPackage (fixedQuarticCoefficients x.parameter)
  | FixedCarrierProjection.companion, x => companionSpectrumPackage x.parameter
  | FixedCarrierProjection.algebraGeometry, x => algebraGeometryPackage x.parameter

def fixedProjectionLedger (_i : FixedCarrierProjection) (_x : FixedQuarticCarrier) :
    ProjectionLedger :=
  emptyProjectionLedger

def FixedQuarticSource : RealityInterface :=
  { Carrier := FixedQuarticCarrier
    classifier := FixedQuarticCarrierRelEquiv
    admissible := FixedQuarticCarrier.admissible
    observations := FixedQuarticCarrier.observations
    ledger := fun _ => emptyProjectionLedger }

def FixedQuarticSpectralCommonCarrier : CommonCarrier FixedCarrierProjection :=
  { source := FixedQuarticSource
    target := fixedTargetInterface
    project := fixedProject
    project_respects := by
      intro i x y same
      cases i
      · exact recurrencePackage_respects same
      · exact resolventPackage_fixed_respects same
      · exact companionSpectrumPackage_respects same
      · exact algebraGeometryPackage_respects same
    projectionLedger := fixedProjectionLedger }

theorem FixedQuarticSpectralCommonCarrier_resolvent_projection
    {x : FixedQuarticCarrier} :
    FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.resolvent x =
      resolventPackage (fixedQuarticCoefficients x.parameter) := by
  rfl

theorem FixedQuarticSpectralCommonCarrier_companion_projection
    {x : FixedQuarticCarrier} :
    FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.companion x =
      companionSpectrumPackage x.parameter := by
  rfl

theorem FixedQuarticSpectralCommonCarrier_algebraGeometry_projection
    {x : FixedQuarticCarrier} :
    FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.algebraGeometry x =
      algebraGeometryPackage x.parameter := by
  rfl

theorem FixedQuarticSpectralCommonCarrier_connection
    {x y : FixedQuarticCarrier} :
    FixedQuarticCarrier.rel x y ->
      RecurrencePackage.rel
        (FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.recurrence x)
        (FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.recurrence y) ∧
      ResolventPackage.rel
        (FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.resolvent x)
        (FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.resolvent y) ∧
      CompanionSpectrumPackage.rel
        (FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.companion x)
        (FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.companion y) ∧
      AlgebraGeometryPackage.rel
        (FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.algebraGeometry x)
        (FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.algebraGeometry y) := by
  intro same
  exact
    ⟨BEDC.Derived.CommonCarrierProjectionUp.projection_preserves_classified_identity
        FixedQuarticSpectralCommonCarrier FixedCarrierProjection.recurrence same,
      BEDC.Derived.CommonCarrierProjectionUp.projection_preserves_classified_identity
        FixedQuarticSpectralCommonCarrier FixedCarrierProjection.resolvent same,
      BEDC.Derived.CommonCarrierProjectionUp.projection_preserves_classified_identity
        FixedQuarticSpectralCommonCarrier FixedCarrierProjection.companion same,
      BEDC.Derived.CommonCarrierProjectionUp.projection_preserves_classified_identity
        FixedQuarticSpectralCommonCarrier FixedCarrierProjection.algebraGeometry same⟩

theorem FixedQuarticSpectralCommonCarrier_algebraGeometry_instance
    (x : FixedQuarticCarrier) :
    AlgebraGeometryPackage.admissible
      (FixedQuarticSpectralCommonCarrier.project FixedCarrierProjection.algebraGeometry x) := by
  exact
    ⟨QuarticCoefficientsRelEquiv.refl (fixedQuarticCoefficients x.parameter),
      BalancedQuarticRows_rel_refl canonicalBalancedQuarticRows,
      BEDC.Derived.PolynomialUp.PolyEq_refl canonicalWeierstrassCubic⟩

end BEDC.Derived.QuarticSpectralCarrierUp
