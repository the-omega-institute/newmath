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

def etaTerms64 : List EtaDyTerm :=
  etaTerms16 ++
  [ { amp := 125246, cos := -1046825, sin := -60573, positive := true }
  , { amp := 119990, cos := -847659, sin := -617241, positive := false }
  , { amp := 115222, cos := -409050, sin := -965500, positive := true }
  , { amp := 110873, cos := 117396, sin := -1041984, positive := false }
  , { amp := 106890, cos := 592152, sin := -865371, positive := true }
  , { amp := 103225, cos := 917432, sin := -507769, positive := false }
  , { amp := 99840, cos := 1046627, sin := -63907, positive := true }
  , { amp := 96703, cos := 979645, sin := 373908, positive := false }
  , { amp := 93787, cos := 750714, sin := 732079, positive := true }
  , { amp := 91069, cos := 413889, sin := 963435, positive := false }
  , { amp := 88527, cos := 29728, sin := 1048155, positive := true }
  , { amp := 86145, cos := -345059, sin := 990175, positive := false }
  , { amp := 83908, cos := -664408, sin := 811217, positive := true }
  , { amp := 81801, cos := -896369, sin := 544090, positive := false }
  , { amp := 79814, cos := -1023838, sin := 226422, positive := true }
  , { amp := 77936, cos := -1043354, sin := -104516, positive := false }
  , { amp := 76158, cos := -962689, sin := -415621, positive := true }
  , { amp := 74472, cos := -797869, sin := -680380, positive := false }
  , { amp := 72870, cos := -570107, sin := -880051, positive := true }
  , { amp := 71347, cos := -302982, sin := -1003849, positive := false }
  , { amp := 69895, cos := -20065, sin := -1048384, positive := true }
  , { amp := 68511, cos := 256928, sin := -1016612, positive := false }
  , { amp := 67190, cos := 509419, sin := -916517, positive := true }
  , { amp := 65926, cos := 722750, sin := -759700, positive := false }
  , { amp := 64716, cos := 886517, sin := -559999, positive := true }
  , { amp := 63557, cos := 994546, sin := -332250, positive := false }
  , { amp := 62445, cos := 1044600, sin := -91227, positive := true }
  , { amp := 61378, cos := 1037905, sin := 149212, positive := false }
  , { amp := 60352, cos := 978556, sin := 376749, positive := true }
  , { amp := 59365, cos := 872875, sin := 581034, positive := false }
  , { amp := 58415, cos := 728770, sin := 753927, positive := true }
  , { amp := 57500, cos := 555120, sin := 889580, positive := false }
  , { amp := 56618, cos := 361234, sin := 984389, positive := true }
  , { amp := 55766, cos := 156364, sin := 1036852, positive := false }
  , { amp := 54944, cos := -50677, sin := 1047351, positive := true }
  , { amp := 54150, cos := -251824, sin := 1017888, positive := false }
  , { amp := 53382, cos := -439989, sin := 951799, positive := true }
  , { amp := 52639, cos := -609202, sin := 853455, positive := false }
  , { amp := 51919, cos := -754699, sin := 727970, positive := true }
  , { amp := 51222, cos := -872942, sin := 580934, positive := false }
  , { amp := 50547, cos := -961591, sin := 418157, positive := true }
  , { amp := 49892, cos := -1019443, sin := 245453, positive := false }
  , { amp := 49256, cos := -1046339, sin := 68455, positive := true }
  , { amp := 48639, cos := -1043047, sin := -107542, positive := false }
  , { amp := 48040, cos := -1011135, sin := -277701, positive := true }
  , { amp := 47458, cos := -952840, sin := -437730, positive := false }
  , { amp := 46892, cos := -870929, sin := -583947, positive := true }
  , { amp := 46341, cos := -768569, sin := -713311, positive := false }
  ]

def level2PartialRe : DyInt :=
  etaDyPartialRe etaTerms64

def level2PartialIm : DyInt :=
  etaDyPartialIm etaTerms64

def level2TailReEnvelope : DyInt :=
  50000

def level2TailImEnvelope : DyInt :=
  50000

def level2ReLower : DyInt :=
  120000

def level2ImAbsLower : DyInt :=
  1000000

structure CenterTailEnvelope where
  etaRe : DyInt
  etaIm : DyInt
  reTailBound : DyInt
  imTailBound : DyInt
  re_tail_lower : level2PartialRe - reTailBound <= etaRe
  re_tail_upper : etaRe <= level2PartialRe + reTailBound
  im_tail_lower : level2PartialIm - imTailBound <= etaIm
  im_tail_upper : etaIm <= level2PartialIm + imTailBound

theorem level2_partial_re_readback :
    level2PartialRe = 181382 := by
  decide

theorem level2_partial_im_readback :
    level2PartialIm = 1077161 := by
  decide

theorem level2_center_minus_tail_re_lower :
    level2ReLower <= level2PartialRe - level2TailReEnvelope := by
  decide

theorem level2_center_minus_tail_im_abs_lower :
    level2ImAbsLower <= level2PartialIm - level2TailImEnvelope := by
  decide

def level3BoxSide : DyInt :=
  65536

def level3BoxRadius : DyInt :=
  32768

def level3DerivativeBound : DyInt :=
  16777216

def level3VariationBound : DyInt :=
  dyMulDown level3DerivativeBound level3BoxRadius

def level3BoxImLower : DyInt :=
  level2ImAbsLower - level3VariationBound

theorem level3_box_side_readback :
    level3BoxSide = 65536 := by
  decide

theorem level3_box_radius_readback :
    level3BoxRadius = 32768 := by
  decide

theorem level3_variation_bound_readback :
    level3VariationBound = 524288 := by
  decide

theorem level3_box_im_lower_readback :
    level3BoxImLower = 475712 := by
  decide

theorem level3_box_im_lower_positive :
    0 < level3BoxImLower := by
  decide

def level3BoxImFloor : Nat :=
  475712

structure SingleBoxPointCertificate where
  pointImFloor : Nat
  point_floor : level3BoxImFloor <= pointImFloor

theorem level3_single_box_im_positive
    (cert : SingleBoxPointCertificate) :
    0 < cert.pointImFloor :=
  Nat.lt_of_lt_of_le (by decide) cert.point_floor

end BEDC.Derived.RHRoute.GombocSingleBoxGate
