namespace BEDC.Derived.RHRoute.GombocSingleBoxGate

/-!
Single-box fixed-point replay data for the windowed Gomboc barrier route.

All numeric entries below use the common denominator `2^20`.  The offline
generator used Python `math.log`, `math.cos`, and `math.sin` at the point
`s = 3/4 + 10 i`, with amplitudes `round(n^(-3/4) * 2^20)` and trigonometric
centers `round(cos(10 log n) * 2^20)`, `round(sin(10 log n) * 2^20)`.
The kernel replay here recomputes each term as a dyadic product and then folds
the signed partial sum.
-/

abbrev DyInt : Type :=
  Int

def dyadicPrecision : Nat :=
  20

def dyadicScale : DyInt :=
  1048576

def dyMulDown (x y : DyInt) : DyInt :=
  (x * y) / dyadicScale

def signedBy (positive : Bool) (x : DyInt) : DyInt :=
  if positive then x else -x

structure EtaDyTerm where
  amp : DyInt
  cos : DyInt
  sin : DyInt
  positive : Bool

def EtaDyTerm.reContribution (t : EtaDyTerm) : DyInt :=
  signedBy t.positive (dyMulDown t.amp t.cos)

def EtaDyTerm.imContribution (t : EtaDyTerm) : DyInt :=
  signedBy t.positive (dyMulDown t.amp (-t.sin))

def etaDyPartialRe (terms : List EtaDyTerm) : DyInt :=
  terms.foldl (fun acc term => acc + term.reContribution) 0

def etaDyPartialIm (terms : List EtaDyTerm) : DyInt :=
  terms.foldl (fun acc term => acc + term.imContribution) 0

def etaTerms16 : List EtaDyTerm :=
  [ { amp := 1048576, cos := 1048576, sin := 0, positive := true }
  , { amp := 623487, cos := 835840, sin := 633153, positive := false }
  , { amp := 460001, cos := -9910, sin := -1048529, positive := true }
  , { amp := 370728, cos := 283954, sin := 1009397, positive := false }
  , { amp := 313597, cos := -971260, sin := -395178, positive := true }
  , { amp := 273518, cos := 625225, sin := -841787, positive := false }
  , { amp := 243656, cos := 859736, sin := 600304, positive := true }
  , { amp := 220436, cos := -383150, sin := 976067, positive := false }
  , { amp := 201799, cos := -1048389, sin := 19820, positive := true }
  , { amp := 186466, cos := -535594, sin := -901472, positive := false }
  , { amp := 173602, cos := 424701, sin := -958718, positive := true }
  , { amp := 162635, cos := 1006668, sin := -293481, positive := false }
  , { amp := 153159, cos := 911662, sin := 518059, positive := true }
  , { amp := 144878, cos := 322836, sin := 997642, positive := false }
  , { amp := 137572, cos := -385981, sin := 974952, positive := true }
  , { amp := 131072, cos := -894787, sin := 546688, positive := false }
  ]

def level1PartialRe : DyInt :=
  etaDyPartialRe etaTerms16

def level1PartialIm : DyInt :=
  etaDyPartialIm etaTerms16

def level1ReLower : DyInt :=
  200000

theorem level1_partial_re_readback :
    level1PartialRe = 231023 := by
  decide

theorem level1_partial_im_readback :
    level1PartialIm = 1109321 := by
  decide

theorem level1_re_lower :
    level1ReLower <= level1PartialRe := by
  decide

end BEDC.Derived.RHRoute.GombocSingleBoxGate
