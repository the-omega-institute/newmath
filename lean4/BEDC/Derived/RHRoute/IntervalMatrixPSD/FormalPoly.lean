import BEDC.Derived.RHRoute.IntervalMatrixPSD.HornerInterval

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

namespace BEDC.Derived.RHRoute.IntervalMatrixPSD.FormalPoly

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PadicUp
open BEDC.Derived.RationalUp
open BEDC.Derived.RHRoute.IntervalMatrixPSD
open BEDC.Real.RatNumKernel

abbrev BRat : Type :=
  BEDC.Derived.RationalUp.RatNum

structure QRat where
  num : Int
  den : Nat
  deriving DecidableEq, Repr

def qraw (num : Int) (den : Nat) : QRat :=
  { num := num, den := den }

def intAbsNat : Int -> Nat
  | Int.ofNat n => n
  | Int.negSucc n => Nat.succ n

def intIsNeg : Int -> Bool
  | Int.ofNat _ => false
  | Int.negSucc _ => true

def qzero : QRat :=
  qraw 0 1

def qone : QRat :=
  qraw 1 1

def qnormalize (num : Int) (den : Nat) : QRat :=
  if den = 0 then qzero else
    let g := Nat.gcd (intAbsNat num) den
    let n := intAbsNat num / g
    let d := den / g
    { num := if intIsNeg num then -Int.ofNat n else Int.ofNat n
      den := d }

def qOfNat (n : Nat) : QRat :=
  qraw (Int.ofNat n) 1

def qOfNatOverNat (num den : Nat) : QRat :=
  qnormalize (Int.ofNat num) den

def qOfIntOverNat (num : Int) (den : Nat) : QRat :=
  qnormalize num den

def qneg (x : QRat) : QRat :=
  qraw (-x.num) x.den

def qadd (x y : QRat) : QRat :=
  qnormalize (x.num * Int.ofNat y.den + y.num * Int.ofNat x.den)
    (x.den * y.den)

def qsub (x y : QRat) : QRat :=
  qadd x (qneg y)

def qmul (x y : QRat) : QRat :=
  qnormalize (x.num * y.num) (x.den * y.den)

def qdivNat (x : QRat) (n : Nat) : QRat :=
  qnormalize x.num (x.den * n)

def qIsZero (x : QRat) : Bool :=
  if x.num = 0 then true else false

private theorem natToUnary_pos_den {n : Nat} :
    0 < n ->
      NatUnaryStrictPrefix NatOne (natToUnary n) ∨
        hsame (natToUnary n) NatOne := by
  intro h
  cases n with
  | zero =>
      cases h
  | succ n =>
      cases n with
      | zero =>
          exact Or.inr rfl
      | succ n =>
          apply Or.inl
          apply NatUnaryStrictPrefix_of_length_lt
          · exact unary_e1_closed unary_empty
          · exact natToUnary_unary (Nat.succ (Nat.succ n))
          · rw [NatUp_unary_standard_bridge.right.left BHist.Empty unary_empty]
            rw [natToUnary_length]
            exact Nat.succ_lt_succ (Nat.zero_lt_succ n)

def intToBEDC : Int -> BEDC.Derived.PrimeUp.IntegerUp
  | Int.ofNat n => intOfNat (natToUnary n) (natToUnary_unary n)
  | Int.negSucc n =>
      intOfNatWithSign BMark.b1 (natToUnary (Nat.succ n))
        (natToUnary_unary (Nat.succ n))

def qToBRat (x : QRat) : BRat :=
  match x.den with
  | 0 => ratZero
  | Nat.succ d =>
      { num := intToBEDC x.num
        den := natToUnary (Nat.succ d)
        den_pos := natToUnary_pos_den (Nat.succ_pos d) }

abbrev Poly : Type :=
  List QRat

def polyConst (x : QRat) : Poly :=
  if qIsZero x then [] else [x]

def polyTrim : Poly -> Poly
  | [] => []
  | a :: rest =>
      let tail := polyTrim rest
      if qIsZero a && tail.isEmpty then [] else a :: tail

def addRaw : Poly -> Poly -> Poly
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => qadd a b :: addRaw as bs

def add (p q : Poly) : Poly :=
  polyTrim (addRaw p q)

def neg (p : Poly) : Poly :=
  polyTrim (p.map qneg)

def sub (p q : Poly) : Poly :=
  add p (neg q)

def scale (a : QRat) (p : Poly) : Poly :=
  if qIsZero a then [] else polyTrim (p.map (fun x => qmul a x))

def mulRaw (p q : Poly) : Poly :=
  match p with
  | [] => []
  | a :: as => add (scale a q) (qzero :: mulRaw as q)

def mul (p q : Poly) : Poly :=
  polyTrim (mulRaw p q)

def pow (p : Poly) (n : Nat) : Poly :=
  match n with
  | 0 => [qone]
  | Nat.succ m => mul (pow p m) p

def eval (p : Poly) (x : QRat) : QRat :=
  match p with
  | [] => qzero
  | a :: rest => qadd a (qmul x (eval rest x))

def derivFrom (n : Nat) (p : Poly) : Poly :=
  match p with
  | [] => []
  | a :: rest => qmul (qOfNat n) a :: derivFrom (n + 1) rest

def deriv (p : Poly) : Poly :=
  match p with
  | [] => []
  | _ :: rest => polyTrim (derivFrom 1 rest)

def antiderivFrom (n : Nat) (p : Poly) : Poly :=
  match p with
  | [] => []
  | a :: rest => qdivNat a n :: antiderivFrom (n + 1) rest

def antideriv (p : Poly) : Poly :=
  qzero :: antiderivFrom 1 p

def composeAffineFrom (affine power p : Poly) : Poly :=
  match p with
  | [] => []
  | a :: rest => add (scale a power) (composeAffineFrom affine (mul power affine) rest)

def composeAffine (p : Poly) (alpha beta : QRat) : Poly :=
  composeAffineFrom (polyTrim [beta, alpha]) [qone] p

abbrev BiPoly : Type :=
  List Poly

def polyIsZero (p : Poly) : Bool :=
  (polyTrim p).isEmpty

def biTrim : BiPoly -> BiPoly
  | [] => []
  | a :: rest =>
      let tail := biTrim rest
      if polyIsZero a && tail.isEmpty then [] else polyTrim a :: tail

def biAddRaw : BiPoly -> BiPoly -> BiPoly
  | [], q => q
  | p, [] => p
  | a :: as, b :: bs => add a b :: biAddRaw as bs

def biAdd (p q : BiPoly) : BiPoly :=
  biTrim (biAddRaw p q)

def biNeg (p : BiPoly) : BiPoly :=
  biTrim (p.map neg)

def biSub (p q : BiPoly) : BiPoly :=
  biAdd p (biNeg q)

def biScalePoly (a : Poly) (p : BiPoly) : BiPoly :=
  if polyIsZero a then [] else biTrim (p.map (fun x => mul a x))

def biMulRaw (p q : BiPoly) : BiPoly :=
  match p with
  | [] => []
  | a :: as => biAdd (biScalePoly a q) ([] :: biMulRaw as q)

def biMul (p q : BiPoly) : BiPoly :=
  biTrim (biMulRaw p q)

def biComposeFrom (t power : BiPoly) (p : Poly) : BiPoly :=
  match p with
  | [] => []
  | a :: rest =>
      biAdd (biScalePoly (polyConst a) power)
        (biComposeFrom t (biMul power t) rest)

def biCompose (p : Poly) (t : BiPoly) : BiPoly :=
  biComposeFrom t [[qone]] p

def evalU (u : Poly) (p : BiPoly) : Poly :=
  match p with
  | [] => []
  | a :: rest => add a (mul u (evalU u rest))

def antiderivUFrom (n : Nat) (p : BiPoly) : BiPoly :=
  match p with
  | [] => []
  | a :: rest => scale (qOfNatOverNat 1 n) a :: antiderivUFrom (n + 1) rest

def antiderivU (p : BiPoly) : BiPoly :=
  [] :: antiderivUFrom 1 p

def bumpBase : Poly :=
  [qone, qzero, qneg (qOfNatOverNat 256 25)]

def bump : Poly :=
  pow bumpBase 5

def qBump : Poly :=
  add (scale (qneg qone) (deriv (deriv bump)))
    (scale (qOfNatOverNat 1 4) bump)

def q1Shift : BiPoly :=
  [[qneg (qOfNatOverNat 1 16)], [qone]]

def q2Shift : BiPoly :=
  [[qOfNatOverNat 1 16, qneg qone], [qone]]

def q1 : BiPoly :=
  biCompose qBump q1Shift

def q2 : BiPoly :=
  biCompose qBump q2Shift

def integrand : BiPoly :=
  biMul q1 q2

def formalIntU : BiPoly :=
  antiderivU integrand

def upperEndpoint : Poly :=
  [qOfNatOverNat 3 8]

def lowerEndpoint : Poly :=
  [qneg (qOfNatOverNat 3 8), qone]

def R_formal : Poly :=
  sub (evalU upperEndpoint formalIntU) (evalU lowerEndpoint formalIntU)

def R_formal_reference : Poly :=
  [ qraw (-(24650928984967279017984 : Int)) 30834484100341796875
  , qraw 1114100653043750170263552 30834484100341796875
  , qraw (-(1749844965647239675379712 : Int)) 6166896820068359375
  , qraw 1440046373618903760764928 324573516845703125
  , qraw (-(14331856940281924235034624 : Int)) 324573516845703125
  , qraw 17842484935784105515155456 95462799072265625
  , qraw (-(2787168929099950501920768 : Int)) 8678436279296875
  , qraw 597406840964785767448576 19092559814453125
  , qraw 7969152171020364476841984 19092559814453125
  , qraw 356072850931081168289792 1888275146484375
  , qraw (-(7390292148532083104415744 : Int)) 7343292236328125
  , qraw (-(25490239857757977000804352 : Int)) 66089630126953125
  , qraw 23689877996843243118002176 13217926025390625
  , qraw 33929761019384685345636352 171833038330078125
  , qraw (-(340005080247231118768603136 : Int)) 171833038330078125
  , qraw 332808147088060038414073856 859165191650390625
  , qraw 860361293698174566155681792 859165191650390625
  , qraw (-(124818528715694226502844416 : Int)) 265560150146484375
  , qraw (-(680721749808029873733632 : Int)) 417308807373046875
  , qraw 5442232223602086755958784 7928867340087890625
  , qraw 2361183241434822606848 4404926300048828125
  , qraw (-(18889465931478580854784 : Int)) 92503452301025390625
  ]

theorem R_formal_coefficients :
    R_formal = R_formal_reference := by
  rfl

theorem R_formal_coeff_count :
    R_formal.length = 22 := by
  rfl

def R_formal_horner_coeffs : List BRat :=
  (R_formal.map qToBRat).reverse

def bq (num : Int) (den : Nat) : BRat :=
  qToBRat (qOfIntOverNat num den)

def i_log2 : QInterval :=
  { lo := bq 5 8
    hi := bq 3 4 }

def i_invSqrt2 : QInterval :=
  { lo := bq 7 10
    hi := bq 71 100 }

def R_formal_at_log2_interval : QInterval :=
  let r := hornerInterval R_formal_horner_coeffs i_log2.lo i_log2.hi
  { lo := r.1, hi := r.2 }

def p2_positive_product_interval : QInterval :=
  intervalMul (intervalMul i_log2 i_invSqrt2) R_formal_at_log2_interval

private theorem ratLe_neg_anti {a b : BRat} :
    ratLe a b -> ratLe (ratNeg b) (ratNeg a) := by
  intro h
  let t := ratAdd (ratNeg a) (ratNeg b)
  have shifted : ratLe (ratAdd a t) (ratAdd b t) :=
    BEDC.Derived.LocatedReal.ratLe_add_right_mono
      (x := a) (x' := b) (y := t) h
  have leftEq : RatEq (ratAdd a t) (ratNeg b) := by
    unfold t
    exact RatEq_trans _ _ _
      (RatEq_symm
        (BEDC.Derived.LocatedReal.ratAdd_assoc_local a (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (ratAdd_respects
          (BEDC.Derived.LocatedReal.ratAdd_neg_local a)
          (RatEq_refl (ratNeg b)))
        (ratZero_add_left (ratNeg b)))
  have rightEq : RatEq (ratAdd b t) (ratNeg a) := by
    unfold t
    exact RatEq_trans _ _ _
      (ratAdd_respects (RatEq_refl b) (ratAdd_comm (ratNeg a) (ratNeg b)))
      (RatEq_trans _ _ _
        (RatEq_symm
          (BEDC.Derived.LocatedReal.ratAdd_assoc_local b (ratNeg b) (ratNeg a)))
        (RatEq_trans _ _ _
          (ratAdd_respects
            (BEDC.Derived.LocatedReal.ratAdd_neg_local b)
            (RatEq_refl (ratNeg a)))
          (ratZero_add_left (ratNeg a))))
  exact ratLe_respects leftEq rightEq shifted

def intervalNeg (I : QInterval) : QInterval :=
  { lo := ratNeg I.hi
    hi := ratNeg I.lo }

theorem intervalNeg_encloses {I : QInterval} {x : BRat} :
    InInterval x I -> InInterval (ratNeg x) (intervalNeg I) := by
  intro hx
  constructor
  · exact ratLe_neg_anti hx.right
  · exact ratLe_neg_anti hx.left

def p2OffDiagEntry : QInterval :=
  intervalNeg p2_positive_product_interval

def R_formal_horner_value (x : BRat) : BRat :=
  hornerEval R_formal_horner_coeffs x

def p2EntryValue (log2Value invSqrt2Value : BRat) : BRat :=
  ratNeg
    (ratMul (ratMul log2Value invSqrt2Value)
      (R_formal_horner_value log2Value))

structure BrickBChamberCert where
  log2Value : BRat
  invSqrt2Value : BRat
  log2_in_interval : InInterval log2Value i_log2
  invSqrt2_in_interval : InInterval invSqrt2Value i_invSqrt2

-- The formal endpoint difference is primitive QRat algebra; analytic Weil-overlap
-- interpretation is carried by this boundary surface.
inductive BrickBSemanticsObligation where
  | formalEndpointPrimitiveMatchesWeilOverlap
  | rationalLogTwoChamberCertificate
  | inverseSqrtTwoRationalWindowCertificate

theorem p2_entry_encloses (cert : BrickBChamberCert) :
    InInterval
      (p2EntryValue cert.log2Value cert.invSqrt2Value)
      p2OffDiagEntry := by
  have hR :
      InInterval
        (R_formal_horner_value cert.log2Value)
        R_formal_at_log2_interval := by
    unfold R_formal_at_log2_interval R_formal_horner_value
    exact hornerInterval_encloses R_formal_horner_coeffs
      i_log2.lo i_log2.hi cert.log2Value
      cert.log2_in_interval.left cert.log2_in_interval.right
  have hLogSqrt :
      InInterval (ratMul cert.log2Value cert.invSqrt2Value)
        (intervalMul i_log2 i_invSqrt2) :=
    intervalMul_encloses cert.log2_in_interval cert.invSqrt2_in_interval
  have hProduct :
      InInterval
        (ratMul (ratMul cert.log2Value cert.invSqrt2Value)
          (R_formal_horner_value cert.log2Value))
        p2_positive_product_interval := by
    unfold p2_positive_product_interval
    exact intervalMul_encloses hLogSqrt hR
  unfold p2EntryValue p2OffDiagEntry
  exact intervalNeg_encloses hProduct

end BEDC.Derived.RHRoute.IntervalMatrixPSD.FormalPoly
