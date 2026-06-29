import BEDC.Real.ZetaCertPowBoxes
import BEDC.Real.ZetaCertHasse24
import BEDC.Derived.RHRoute.ZetaBoxKrawczyk

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace BEDC
namespace ZetaCert
namespace Zeta14

structure V2 where
  x : Dy.I
  y : Dy.I
deriving Repr, DecidableEq

namespace V2

def neg (v : V2) : V2 :=
  { x := Dy.neg v.x, y := Dy.neg v.y }

def ofC (z : CBox) : V2 :=
  { x := z.re, y := z.im }

end V2

structure M2 where
  xx : Dy.I
  xy : Dy.I
  yx : Dy.I
  yy : Dy.I
deriving Repr, DecidableEq

namespace M2

def ident : M2 :=
  { xx := Dy.one, xy := Dy.zero, yx := Dy.zero, yy := Dy.one }

def add (A B : M2) : M2 :=
  { xx := Dy.add A.xx B.xx, xy := Dy.add A.xy B.xy,
    yx := Dy.add A.yx B.yx, yy := Dy.add A.yy B.yy }

def neg (A : M2) : M2 :=
  { xx := Dy.neg A.xx, xy := Dy.neg A.xy,
    yx := Dy.neg A.yx, yy := Dy.neg A.yy }

def sub (A B : M2) : M2 :=
  add A (neg B)

def mul (A B : M2) : M2 :=
  { xx := Dy.add (Dy.mul A.xx B.xx) (Dy.mul A.xy B.yx),
    xy := Dy.add (Dy.mul A.xx B.xy) (Dy.mul A.xy B.yy),
    yx := Dy.add (Dy.mul A.yx B.xx) (Dy.mul A.yy B.yx),
    yy := Dy.add (Dy.mul A.yx B.xy) (Dy.mul A.yy B.yy) }

def vecMul (A : M2) (v : V2) : V2 :=
  { x := Dy.add (Dy.mul A.xx v.x) (Dy.mul A.xy v.y),
    y := Dy.add (Dy.mul A.yx v.x) (Dy.mul A.yy v.y) }

def jacOfComplexDeriv (fp : CBox) : M2 :=
  { xx := fp.re, xy := Dy.neg fp.im, yx := fp.im, yy := fp.re }

def complexMulMatrix (a : CBox) : M2 :=
  { xx := a.re, xy := Dy.neg a.im, yx := a.im, yy := a.re }

def det (A : M2) : Dy.I :=
  Dy.sub (Dy.mul A.xx A.yy) (Dy.mul A.xy A.yx)

def detNonzero (A : M2) : Bool :=
  let d := det A
  decide (d.hi < 0 || 0 < d.lo)

def row0Mag (A : M2) : Int :=
  Dy.mag A.xx + Dy.mag A.xy

def row1Mag (A : M2) : Int :=
  Dy.mag A.yx + Dy.mag A.yy

def opMagInf (A : M2) : Int :=
  max (row0Mag A) (row1Mag A)

def contract125 (A : M2) : Bool :=
  Dy.leInv125 (opMagInf A)

end M2

def rowBallBound (rowMag : Int) (rad : Int) : Int :=
  Dy.ceilS (rowMag * rad)

def mapsBallInf (q : V2) (R : M2) (rad : Int) : Bool :=
  let bx := Dy.mag q.x + rowBallBound (M2.row0Mag R) rad
  let byBound := Dy.mag q.y + rowBallBound (M2.row1Mag R) rad
  decide (bx <= rad /\ byBound <= rad)

def coeff24 (i : Nat) : Dy.I :=
  Hasse24.coeff24N i

def etaTerm (pow : Array CBox) (i : Nat) : CBox :=
  CBox.smul (coeff24 i) (pow.getD i CBox.zero)

def derivTerm (pow : Array CBox) (lns : Array Dy.I) (i : Nat) : CBox :=
  let a := coeff24 i
  let L := lns.getD i Dy.zero
  let c := Dy.neg (Dy.mul a L)
  CBox.smul c (pow.getD i CBox.zero)

def add6 (a b c d e f : CBox) : CBox :=
  CBox.add (CBox.add (CBox.add a b) (CBox.add c d)) (CBox.add e f)

def etaBlock (pow : Array CBox) (lo : Nat) : CBox :=
  add6
    (etaTerm pow lo)
    (etaTerm pow (lo + 1))
    (etaTerm pow (lo + 2))
    (etaTerm pow (lo + 3))
    (etaTerm pow (lo + 4))
    (etaTerm pow (lo + 5))

def derivBlock (pow : Array CBox) (lns : Array Dy.I) (lo : Nat) : CBox :=
  add6
    (derivTerm pow lns lo)
    (derivTerm pow lns (lo + 1))
    (derivTerm pow lns (lo + 2))
    (derivTerm pow lns (lo + 3))
    (derivTerm pow lns (lo + 4))
    (derivTerm pow lns (lo + 5))

structure BlockOut where
  eta : CBox
  der : CBox
deriving Repr, DecidableEq

def checkBlock (pow : Array CBox) (lns : Array Dy.I)
    (lo : Nat) (b : BlockOut) : Bool :=
  CBox.eqb b.eta (etaBlock pow lo) &&
    CBox.eqb b.der (derivBlock pow lns lo)

def sumBlocks (b0 b1 b2 b3 : CBox) : CBox :=
  CBox.add (CBox.add b0 b1) (CBox.add b2 b3)

structure Cert where
  sig0 : Int
  tau0 : Int
  rad : Int
  A : CBox
  lns : Array Dy.I
  powC : Array CBox
  b0 : BlockOut
  b1 : BlockOut
  b2 : BlockOut
  b3 : BlockOut
deriving Repr, DecidableEq

namespace Cert

def sizeCheck (c : Cert) : Bool :=
  decide (c.lns.size = 24 /\ c.powC.size = 24)

def checkBlock0 (c : Cert) : Bool :=
  checkBlock c.powC c.lns 0 c.b0

def checkBlock1 (c : Cert) : Bool :=
  checkBlock c.powC c.lns 6 c.b1

def checkBlock2 (c : Cert) : Bool :=
  checkBlock c.powC c.lns 12 c.b2

def checkBlock3 (c : Cert) : Bool :=
  checkBlock c.powC c.lns 18 c.b3

def eta24Center (c : Cert) : CBox :=
  sumBlocks c.b0.eta c.b1.eta c.b2.eta c.b3.eta

def eta24DerivBall (c : Cert) : CBox :=
  sumBlocks c.b0.der c.b1.der c.b2.der c.b3.der

def J (c : Cert) : M2 :=
  M2.jacOfComplexDeriv (eta24DerivBall c)

def A2 (c : Cert) : M2 :=
  M2.complexMulMatrix c.A

def q (c : Cert) : V2 :=
  V2.neg (M2.vecMul (A2 c) (V2.ofC (eta24Center c)))

def R (c : Cert) : M2 :=
  M2.sub M2.ident (M2.mul (A2 c) (J c))

def checkMaps (c : Cert) : Bool :=
  mapsBallInf (q c) (R c) c.rad

def checkContract (c : Cert) : Bool :=
  M2.contract125 (R c)

def checkDetA (c : Cert) : Bool :=
  M2.detNonzero (A2 c)

def checkCore (c : Cert) : Bool :=
  sizeCheck c &&
    Dy.posMant c.rad &&
    PowBoxes.tableOk &&
    checkBlock0 c &&
    checkBlock1 c &&
    checkBlock2 c &&
    checkBlock3 c &&
    checkDetA c &&
    checkMaps c &&
    checkContract c

end Cert

def sig0 : Int :=
  39614081257132168796771975168

def tau0 : Int :=
  1119866308690372132583465674814

def rad : Int :=
  79228162514264339242811392

def inverseEta24Deriv : CBox :=
  { re := { lo := 41982441694965696139280213242,
            hi := 41982441694965696139280213243 },
    im := { lo := 2564259429375206334736378510,
            hi := 2564259429375206334736378511 } }

def block0 : BlockOut :=
  { eta := { re := { lo := -63935550605650572106448662, hi := -63935550605650571107295719 }, im := { lo := 28827517451279724915485383679, hi := 28827517451279724916484536624 } },
    der := { re := { lo := 151707683626701878390301155866, hi := 151707683626701878391620166499 }, im := { lo := -64389881064666887614907204636, hi := -64389881064666887613590660324 } } }

def block1 : BlockOut :=
  { eta := { re := { lo := 1900950635088530248566783351, hi := 1900950635088530249574214130 }, im := { lo := -35088013656729225839171165314, hi := -35088013656729225838163734534 } },
    der := { re := { lo := -7642492140874461065408184622, hi := -7642492140874461063184349068 }, im := { lo := 71229648856450300029571206450, hi := 71229648856450300031795058125 } } }

def block2 : BlockOut :=
  { eta := { re := { lo := -1828546459034294551852062954, hi := -1828546459034294551659493715 }, im := { lo := 6264130328645139924500817568, hi := 6264130328645139924693386808 } },
    der := { re := { lo := 4776583770401943475634191277, hi := 4776583770401943476142380425 }, im := { lo := -15849314444943471204344687548, hi := -15849314444943471203836367878 } } }

def block3 : BlockOut :=
  { eta := { re := { lo := -40739391028836821566376481, hi := -40739391028836821565529398 }, im := { lo := 30377969284585400004664640, hi := 30377969284585400005511725 } },
    der := { re := { lo := 119805731075956935576917885, hi := 119805731075956935579424485 }, im := { lo := -88926976284428716986552396, hi := -88926976284428716984045482 } } }

def zero14Cert : Cert :=
  { sig0 := sig0
    tau0 := tau0
    rad := rad
    A := inverseEta24Deriv
    lns := #[
      { lo := 0, hi := 0 },
      { lo := 54916777467707473351140471128, hi := 54916777467707473351142471129 },
      { lo := 87041032946764879767664216853, hi := 87041032946764879767666216854 },
      { lo := 109833554935414946702281942256, hi := 109833554935414946702283942257 },
      { lo := 127512808482947240738987467478, hi := 127512808482947240738989467479 },
      { lo := 141957810414472353118805687981, hi := 141957810414472353118807687982 },
      { lo := 154170885527510703318126384271, hi := 154170885527510703318128384272 },
      { lo := 164750332403122420053423413384, hi := 164750332403122420053425413385 },
      { lo := 174082065893529759535329433706, hi := 174082065893529759535331433707 },
      { lo := 182429585950654714090128938606, hi := 182429585950654714090130938607 },
      { lo := 189980836365455518885311199060, hi := 189980836365455518885313199061 },
      { lo := 196874587882179826469947159109, hi := 196874587882179826469949159110 },
      { lo := 203216224533820523568939310292, hi := 203216224533820523568941310293 },
      { lo := 209087662995218176669267855399, hi := 209087662995218176669269855400 },
      { lo := 214553841429712120506652684331, hi := 214553841429712120506654684332 },
      { lo := 219667109870829893404564884512, hi := 219667109870829893404566884513 },
      { lo := 224470287260468208355273622743, hi := 224470287260468208355275622744 },
      { lo := 228998843361237232886470904834, hi := 228998843361237232886472904835 },
      { lo := 233282489954733330934589005870, hi := 233282489954733330934591005871 },
      { lo := 237346363418362187441270409734, hi := 237346363418362187441272409735 },
      { lo := 241211918474275583085791601124, hi := 241211918474275583085793601125 },
      { lo := 244897613833162992236452670189, hi := 244897613833162992236454670190 },
      { lo := 248419445302170508208678951947, hi := 248419445302170508208680951948 },
      { lo := 251791365349887299821088630237, hi := 251791365349887299821090630238 }
    ]
    powC := #[
      { re := { lo := 79228162514264337593543950336, hi := 79228162514264337593543950336 }, im := { lo := 0, hi := 0 } },
      { re := { lo := -52177702825944216137348080201, hi := -52177702825944216137148080200 }, im := { lo := 20397014377128662093336223337, hi := 20397014377128662093536223338 } },
      { re := { lo := -45008211582737569781192541263, hi := -45008211582737569780992541262 }, im := { lo := -8162605910640379047414805745, hi := -8162605910640379047214805744 } },
      { re := { lo := 29111800696835461030387212271, hi := 29111800696835461030587212272 }, im := { lo := -26865935569683787889577774917, hi := -26865935569683787889377774916 } },
      { re := { lo := -25736610400962701519223819865, hi := -25736610400962701519023819864 }, im := { lo := 24352561100352353800333563736, hi := 24352561100352353800533563737 } },
      { re := { lo := 31742726310895819881078278162, hi := 31742726310895819881278278163 }, im := { lo := -6211517440691046409586851903, hi := -6211517440691046409386851902 } },
      { re := { lo := -21509029201497963198447442094, hi := -21509029201497963198247442093 }, im := { lo := -20834838183918354744636963767, hi := -20834838183918354744436963766 } },
      { re := { lo := -12255768411174795112250026972, hi := -12255768411174795112050026971 }, im := { lo := 25187970493372131424437429028, hi := 25187970493372131424637429029 } },
      { re := { lo := 24727456909925562029266081039, hi := 24727456909925562029466081040 }, im := { lo := 9274083412611320586687382783, hi := 9274083412611320586887382784 } },
      { re := { lo := 10680011292858172980038784212, hi := 10680011292858172980238784213 }, im := { lo := -22663793423058946794734662527, hi := -22663793423058946794534662526 } },
      { re := { lo := -18812912297017439960851776315, hi := -18812912297017439960651776314 }, im := { lo := -14721411046927874581015474865, hi := -14721411046927874580815474864 } },
      { re := { lo := -19305838747910592234576131699, hi := -19305838747910592234376131698 }, im := { lo := 12262805613802143821696139694, hi := 12262805613802143821896139695 } },
      { re := { lo := 2771732457916889800513780616, hi := 2771732457916889800713780617 }, im := { lo := 21798428356807269747169265832, hi := 21798428356807269747369265833 } },
      { re := { lo := 19529169661788864255246772041, hi := 19529169661788864255446772042 }, im := { lo := 8183883063164002389792274959, hi := 8183883063164002389992274960 } },
      { re := { lo := 17129504490043420277347211224, hi := 17129504490043420277547211225 }, im := { lo := -11182733339902236165469525136, hi := -11182733339902236165269525135 } },
      { re := { lo := 1586789871028935847040842653, hi := 1586789871028935847240842654 }, im := { lo := -19743377531893258128382567174, hi := -19743377531893258128182567173 } },
      { re := { lo := -13468989915315998154400557261, hi := -13468989915315998154200557260 }, im := { lo := -13705020584197370437056948432, hi := -13705020584197370436856948431 } },
      { re := { lo := -18672470293916130699423136443, hi := -18672470293916130699223136442 }, im := { lo := 258316300237865243172467387, hi := 258316300237865243372467388 } },
      { re := { lo := -12946508469265821107355252524, hi := -12946508469265821107155252523 }, im := { lo := 12757809138010169112104951411, hi := 12757809138010169112304951412 } },
      { re := { lo := -1198875906139732961661910710, hi := -1198875906139732961461910709 }, im := { lo := 17675343938124985532443845617, hi := 17675343938124985532643845618 } },
      { re := { lo := 10072382579734037883485472151, hi := 10072382579734037883685472152 }, im := { lo := 14051929248841779101268225564, hi := 14051929248841779101468225565 } },
      { re := { lo := 16179693422390599168843988028, hi := 16179693422390599169043988029 }, im := { lo := 4851837477841814007053724374, hi := 4851837477841814007253724375 } },
      { re := { lo := 15591114228903221039586494963, hi := 15591114228903221039786494964 }, im := { lo := -5462108004903799146077222080, hi := -5462108004903799145877222079 } },
      { re := { lo := 9557330001804503275136485287, hi := 9557330001804503275336485288 }, im := { lo := -13046200553330430536972977058, hi := -13046200553330430536772977057 } }
    ]
    b0 := block0
    b1 := block1
    b2 := block2
    b3 := block3 }

structure CertChecks (c : Cert) where
  size : Cert.sizeCheck c = true
  rad_pos : Dy.posMant c.rad = true
  powboxes : PowBoxes.tableOk = true
  b0 : Cert.checkBlock0 c = true
  b1 : Cert.checkBlock1 c = true
  b2 : Cert.checkBlock2 c = true
  b3 : Cert.checkBlock3 c = true
  detA : Cert.checkDetA c = true
  maps : Cert.checkMaps c = true
  contract : Cert.checkContract c = true

theorem z14_size :
    Cert.sizeCheck zero14Cert = true := by
  decide

theorem z14_rad :
    Dy.posMant zero14Cert.rad = true := by
  decide

theorem z14_powboxes :
    PowBoxes.tableOk = true := by
  decide

theorem z14_b0 :
    Cert.checkBlock0 zero14Cert = true := by
  decide

theorem z14_b1 :
    Cert.checkBlock1 zero14Cert = true := by
  decide

theorem z14_b2 :
    Cert.checkBlock2 zero14Cert = true := by
  decide

theorem z14_b3 :
    Cert.checkBlock3 zero14Cert = true := by
  decide

theorem z14_detA :
    Cert.checkDetA zero14Cert = true := by
  decide

theorem z14_maps :
    Cert.checkMaps zero14Cert = true := by
  decide

theorem z14_contract :
    Cert.checkContract zero14Cert = true := by
  decide

theorem z14_checks :
    CertChecks zero14Cert where
  size := z14_size
  rad_pos := z14_rad
  powboxes := z14_powboxes
  b0 := z14_b0
  b1 := z14_b1
  b2 := z14_b2
  b3 := z14_b3
  detA := z14_detA
  maps := z14_maps
  contract := z14_contract

theorem z14_checkCore :
    Cert.checkCore zero14Cert = true := by
  unfold Cert.checkCore
  rw [z14_size, z14_rad, z14_powboxes, z14_b0, z14_b1,
    z14_b2, z14_b3, z14_detA, z14_maps, z14_contract]
  rfl

inductive RemainingObligation where
  | powBoxAnalyticSoundness
  | etaTailAndEulerFactorBridge
  | dyKrawczykToContractionZeroCert
deriving DecidableEq, Repr

def remainingObligations : List RemainingObligation :=
  [ RemainingObligation.powBoxAnalyticSoundness,
    RemainingObligation.etaTailAndEulerFactorBridge,
    RemainingObligation.dyKrawczykToContractionZeroCert ]

theorem remainingObligations_readback :
    remainingObligations.length = 3 := by
  decide

theorem located_true_zeta_zero_of_bridge_remains :
    remainingObligations =
      [ RemainingObligation.powBoxAnalyticSoundness,
        RemainingObligation.etaTailAndEulerFactorBridge,
        RemainingObligation.dyKrawczykToContractionZeroCert ] := by
  rfl

end Zeta14
end ZetaCert
end BEDC
