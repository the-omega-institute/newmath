import BEDC.Derived.PadicUp
import BEDC.Derived.IntUp.Arithmetic
import BEDC.Derived.NatUp.NatAdd
import BEDC.Derived.PrimeUp.PrimeShape

namespace BEDC.Derived.PadicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.IntUp
open BEDC.Derived.NatUp
open BEDC.Derived.PrimeUp

theorem PPow_exponent_hsame_transport {p n n' r : BHist} :
    PPow p n r -> hsame n n' -> PPow p n' r := by
  intro pow same
  cases same
  exact pow

theorem PPow_result_hsame_transport {p n r r' : BHist} :
    PPow p n r -> hsame r r' -> PPow p n r' := by
  intro pow same
  cases same
  exact pow

theorem PPow_add {p m n s a b r : BHist} :
    PPow p m a -> PPow p n b -> NatAdd m n s -> NatMul a b r ->
      PPow p s r := by
  intro left right
  induction right generalizing s r with
  | zero _hp =>
      intro add product
      have sameS : hsame s m := (cont_right_unit_iff.mp add.right.right)
      have powS : PPow p s a :=
        PPow_exponent_hsame_transport left (hsame_symm sameS)
      have sameR : hsame r a := NatMul_unit_right_hsame product
      exact PPow_result_hsame_transport powS (hsame_symm sameR)
  | succ previous step ih =>
      intro add product
      have pUnary : UnaryHistory p := PPow_prime_unary left
      have aUnary : UnaryHistory a := PPow_result_unary left
      have previousResultUnary : UnaryHistory _ := PPow_result_unary previous
      have productABTotal := NatMul_total aUnary previousResultUnary
      cases productABTotal with
      | intro ab abData =>
          have prevAdd : NatAdd m _ (append m _) :=
            NatAdd_append_self (PPow_exponent_unary left) (PPow_exponent_unary previous)
          have powAB : PPow p (append m _) ab := ih prevAdd abData.right
          have reverseStepTotal := NatMul_total previousResultUnary pUnary
          cases reverseStepTotal with
          | intro bp bpData =>
              have sameStep : hsame _ bp :=
                NatMul_comm_hsame pUnary previousResultUnary step bpData.right
              have productWithReverse : NatMul a bp r :=
                (NatMul_multiplier_hsame_transport product sameStep).right
              have abUnary : UnaryHistory ab := abData.left
              have abRightTotal := NatMul_total abUnary pUnary
              cases abRightTotal with
              | intro abp abpData =>
                  have assocSame : hsame abp r :=
                    NatMul_assoc_hsame aUnary previousResultUnary pUnary
                      abData.right abpData.right bpData.right productWithReverse
                  have pAbTotal := NatMul_total pUnary abUnary
                  cases pAbTotal with
                  | intro pab pabData =>
                      have commSame : hsame abp pab :=
                        NatMul_comm_hsame abUnary pUnary abpData.right pabData.right
                      have samePabR : hsame pab r :=
                        hsame_trans (hsame_symm commSame) assocSame
                      have stepProduct : NatMul p ab r :=
                        (NatMul_result_hsame_transport pabData.right samePabR).right
                      have powStep : PPow p (BHist.e1 (append m _)) r :=
                        PPow.succ powAB stepProduct
                      exact PPow_exponent_hsame_transport powStep (hsame_symm add.right.right)

theorem PDvdNat_cont_closed {p k x y z : BHist} :
    PDvdNat p k x -> PDvdNat p k y -> Cont x y z -> PDvdNat p k z := by
  intro left right continuation
  cases left with
  | intro pk leftData =>
      cases right with
      | intro pk' rightData =>
          have samePower : hsame pk' pk := PPow_functional rightData.left leftData.left
          have rightDividesByLeftPower : NatDivides pk y :=
            (NatDivides_divisor_hsame_transport rightData.right samePower).right
          exact Exists.intro pk
            (And.intro leftData.left
              (NatDivides_cont_closed leftData.right rightDividesByLeftPower continuation))

theorem PDvdNat_product_add {p j k s x y z : BHist} :
    PDvdNat p j x -> PDvdNat p k y -> NatAdd j k s -> NatMul x y z ->
      PDvdNat p s z := by
  intro left right add product
  cases left with
  | intro pj leftData =>
      cases right with
      | intro pk rightData =>
          have pjUnary : UnaryHistory pj := PPow_result_unary leftData.left
          have pkUnary : UnaryHistory pk := PPow_result_unary rightData.left
          have powerProductTotal := NatMul_total pjUnary pkUnary
          cases powerProductTotal with
          | intro pjk pjkData =>
              have powAdd : PPow p s pjk :=
                PPow_add leftData.left rightData.left add pjkData.right
              have xUnary : UnaryHistory x := NatDivides_result_unary leftData.right
              have yUnary : UnaryHistory y := NatDivides_result_unary rightData.right
              exact Exists.intro pjk
                (And.intro powAdd
                  (NatDivides_product_closed pjUnary pkUnary xUnary yUnary
                    leftData.right rightData.right pjkData.right product))

theorem PDvdNat_natMulFn_add {p j k s x y : BHist} :
    PDvdNat p j x -> PDvdNat p k y -> NatAdd j k s ->
      PDvdNat p s (natMulFn x y) := by
  intro left right add
  exact PDvdNat_product_add left right add
    (natMulFn_rel (PDvdNat_dividend_unary left) (PDvdNat_dividend_unary right))

theorem PDvdNat_succ_of_displayed_power_quotient_divides {p k pk x q : BHist} :
    PPow p k pk -> NatMul pk q x -> NatDivides p q ->
      PDvdNat p (BHist.e1 k) x := by
  intro pow productPowerQuotient dividesQuotient
  cases dividesQuotient with
  | intro t tData =>
      have pkPTotal := NatMul_total (PPow_result_unary pow) (PPow_prime_unary pow)
      cases pkPTotal with
      | intro pkNext pkNextData =>
          have nextPow : PPow p (BHist.e1 k) pkNext := by
            have pPkTotal := NatMul_total (PPow_prime_unary pow) (PPow_result_unary pow)
            cases pPkTotal with
            | intro ppk ppkData =>
                have samePpkPkNext : hsame ppk pkNext :=
                  NatMul_comm_hsame (PPow_prime_unary pow) (PPow_result_unary pow)
                    ppkData.right pkNextData.right
                exact PPow_result_hsame_transport (PPow.succ pow ppkData.right) samePpkPkNext
          have pkNextDividesX : NatDivides pkNext x := by
            have pkNextTTotal := NatMul_total pkNextData.left tData.left
            cases pkNextTTotal with
            | intro displayed displayedData =>
                have sameDisplayedX : hsame displayed x :=
                  NatMul_assoc_hsame (PPow_result_unary pow) (PPow_prime_unary pow)
                    tData.left pkNextData.right displayedData.right tData.right
                    productPowerQuotient
                exact
                  (NatDivides_dividend_hsame_transport
                    (Exists.intro t (And.intro tData.left displayedData.right))
                    sameDisplayedX).right
          exact Exists.intro pkNext (And.intro nextPow pkNextDividesX)

def PadicProductExactnessObstruction (p s z : BHist) : Prop :=
  PDvdNat p (BHist.e1 s) z -> False

theorem IsPadicValNat_mul_add_lower_bound {p j k s x y z : BHist} :
    IsPadicValNat p x j -> IsPadicValNat p y k -> NatAdd j k s ->
      NatMul x y z -> PDvdNat p s z := by
  intro left right add product
  exact PDvdNat_product_add left.left right.left add product

theorem IsPadicValNat_mul_add_exact_with_obstruction {p j k s x y z : BHist} :
    IsPadicValNat p x j -> IsPadicValNat p y k -> NatAdd j k s ->
      NatMul x y z -> PadicProductExactnessObstruction p s z ->
        IsPadicValNat p z s := by
  intro left right add product obstruction
  exact And.intro (IsPadicValNat_mul_add_lower_bound left right add product) obstruction

theorem IsPadicValNat_mul_add_exact_obstruction
    {p j k s x y z : BHist} :
    NatEuclidPrime p -> IsPadicValNat p x j -> IsPadicValNat p y k -> NatAdd j k s ->
      NatMul x y z -> PadicProductExactnessObstruction p s z := by
  intro euclid left right add product succDivides
  cases left.left with
  | intro pj leftData =>
      cases right.left with
      | intro pk rightData =>
          cases succDivides with
          | intro psucc succData =>
              cases succData with
              | intro powSucc dividesSucc =>
                  have pUnary : UnaryHistory p := (PDvdNat_power_unary left.left).left
                  have pjUnary : UnaryHistory pj := PPow_result_unary leftData.left
                  have pkUnary : UnaryHistory pk := PPow_result_unary rightData.left
                  have powAddTotal := NatMul_total pjUnary pkUnary
                  cases powAddTotal with
                  | intro ps psData =>
                      have powAdd : PPow p s ps :=
                        PPow_add leftData.left rightData.left add psData.right
                      cases PPow_succ_inversion powSucc with
                      | intro psPred stepData =>
                          have samePsPred : hsame psPred ps :=
                            PPow_functional stepData.left powAdd
                          have pPsTotal := NatMul_total pUnary psData.left
                          cases pPsTotal with
                          | intro pps ppsData =>
                              have stepOnPs : NatMul p ps psucc :=
                                (NatMul_multiplier_hsame_transport stepData.right samePsPred).right
                              have sameSuccPower : hsame psucc pps :=
                                NatMul_functional pUnary stepOnPs ppsData.right
                              have ppsDividesZ : NatDivides pps z :=
                                (NatDivides_divisor_hsame_transport dividesSucc
                                  sameSuccPower).right
                              cases leftData.right with
                              | intro lx lxData =>
                                  cases rightData.right with
                                  | intro ry ryData =>
                                      have quotientTotal := NatMul_total lxData.left ryData.left
                                      cases quotientTotal with
                                      | intro qr qrData =>
                                          have psQRProduct : NatMul ps qr z :=
                                            NatMul_product_factor_quotient pjUnary pkUnary
                                              lxData.left ryData.left lxData.right ryData.right
                                              psData.right qrData.right product
                                          have ppsReverseTotal := NatMul_total psData.left pUnary
                                          cases ppsReverseTotal with
                                          | intro ppsReverse ppsReverseData =>
                                              have samePpsReverse : hsame ppsReverse pps :=
                                                NatMul_comm_hsame psData.left pUnary
                                                  ppsReverseData.right ppsData.right
                                              have ppsReverseDividesZ : NatDivides ppsReverse z :=
                                                (NatDivides_divisor_hsame_transport ppsDividesZ
                                                  (hsame_symm samePpsReverse)).right
                                              have pDividesQR : NatDivides p qr :=
                                                NatDivides_multiplier_after_common_multiplicand_cancel
                                                  psData.left
                                                  (PPow_nonempty_result
                                                    (NatPrime_empty_absurd euclid.left) powAdd)
                                                  pUnary ppsReverseData.right psQRProduct
                                                  ppsReverseDividesZ
                                              have factorCases :=
                                                NatEuclidPrime_product_left_or_right euclid
                                                  lxData.left ryData.left qrData.right pDividesQR
                                              cases factorCases with
                                              | inl pDividesLX =>
                                                  exact left.right
                                                    (PDvdNat_succ_of_displayed_power_quotient_divides
                                                      leftData.left lxData.right pDividesLX)
                                              | inr pDividesRY =>
                                                  exact right.right
                                                    (PDvdNat_succ_of_displayed_power_quotient_divides
                                                      rightData.left ryData.right pDividesRY)

theorem IsPadicValNat_mul_add_exact {p j k s x y z : BHist} :
    NatEuclidPrime p -> IsPadicValNat p x j -> IsPadicValNat p y k -> NatAdd j k s ->
      NatMul x y z -> IsPadicValNat p z s := by
  intro euclid left right add product
  exact IsPadicValNat_mul_add_exact_with_obstruction left right add product
    (IsPadicValNat_mul_add_exact_obstruction euclid left right add product)

theorem IsPadicValNat_mul_add_exact_of_prime {p j k s x y z : BHist} :
    NatPrime p -> IsPadicValNat p x j -> IsPadicValNat p y k -> NatAdd j k s ->
      NatMul x y z -> IsPadicValNat p z s := by
  intro prime left right add product
  exact IsPadicValNat_mul_add_exact (NatPrime.toNatEuclidPrime prime)
    left right add product

theorem IsPadicValNat_add_min_lower {p k x y z : BHist} :
    IsPadicValNat p x k -> IsPadicValNat p y k -> NatAdd x y z ->
      PDvdNat p k z := by
  intro left right add
  exact PDvdNat_cont_closed left.left right.left add.right.right

def IntMagnitudeProduct
    (x y z : BEDC.FKernel.Mark.BMark × BHist) : Prop :=
  IntCarrier x.1 x.2 ∧ IntCarrier y.1 y.2 ∧ IntCarrier z.1 z.2 ∧ NatMul x.2 y.2 z.2

theorem PDvdInt_magnitude_product_add {p j k s : BHist}
    {x y z : BEDC.FKernel.Mark.BMark × BHist} :
    PDvdInt p j x -> PDvdInt p k y -> NatAdd j k s -> IntMagnitudeProduct x y z ->
      PDvdInt p s z := by
  intro left right add product
  exact And.intro product.right.right.left
    (PDvdNat_product_add left.right right.right add product.right.right.right)

theorem IsPadicValInt_magnitude_product_lower_bound {p j k s : BHist}
    {x y z : BEDC.FKernel.Mark.BMark × BHist} :
    IsPadicValInt p x j -> IsPadicValInt p y k -> NatAdd j k s ->
      IntMagnitudeProduct x y z -> PDvdInt p s z := by
  intro left right add product
  exact PDvdInt_magnitude_product_add
    (And.intro left.left left.right.left) (And.intro right.left right.right.left) add product

theorem IsPadicValInt_magnitude_product_exact_with_obstruction {p j k s : BHist}
    {x y z : BEDC.FKernel.Mark.BMark × BHist} :
    IsPadicValInt p x j -> IsPadicValInt p y k -> NatAdd j k s ->
      IntMagnitudeProduct x y z -> PadicProductExactnessObstruction p s z.2 ->
        IsPadicValInt p z s := by
  intro left right add product obstruction
  exact And.intro product.right.right.left
    (IsPadicValNat_mul_add_exact_with_obstruction left.right right.right add
      product.right.right.right obstruction)

theorem IsPadicValInt_magnitude_product_exact {p j k s : BHist}
    {x y z : BEDC.FKernel.Mark.BMark × BHist} :
    NatEuclidPrime p -> IsPadicValInt p x j -> IsPadicValInt p y k -> NatAdd j k s ->
      IntMagnitudeProduct x y z -> IsPadicValInt p z s := by
  intro euclid left right add product
  exact And.intro product.right.right.left
    (IsPadicValNat_mul_add_exact euclid left.right right.right add product.right.right.right)

theorem IsPadicValInt_add_min_lower {p k : BHist}
    {x y z : BEDC.FKernel.Mark.BMark × BHist} :
    IsPadicValInt p x k -> IsPadicValInt p y k ->
      IntCarrier z.1 z.2 -> NatAdd x.2 y.2 z.2 -> PDvdInt p k z := by
  intro left right zCarrier add
  exact And.intro zCarrier (IsPadicValNat_add_min_lower left.right right.right add)

theorem PDvdIntPair_pairMul_add {p j k s : BHist} {x y : BHist × BHist} :
    PDvdIntPair p j x -> PDvdIntPair p k y -> NatAdd j k s ->
      PDvdIntPair p s (pairMul x y) := by
  intro left right add
  cases x with
  | mk xp xn =>
      cases y with
      | mk yp yn =>
          constructor
          · exact pairMul_carrier left.left right.left
          · constructor
            · change PDvdNat p s (append (natMulFn xp yp) (natMulFn xn yn))
              exact PDvdNat_cont_closed
                (PDvdNat_natMulFn_add left.right.left right.right.left add)
                (PDvdNat_natMulFn_add left.right.right right.right.right add)
                (cont_intro rfl)
            · change PDvdNat p s (append (natMulFn xp yn) (natMulFn xn yp))
              exact PDvdNat_cont_closed
                (PDvdNat_natMulFn_add left.right.left right.right.right add)
                (PDvdNat_natMulFn_add left.right.right right.right.left add)
                (cont_intro rfl)

def PadicIntPairProductExactnessObstruction (p s : BHist) (z : BHist × BHist) : Prop :=
  (PDvdNat p (BHist.e1 s) z.1 -> False) ∧
    (PDvdNat p (BHist.e1 s) z.2 -> False)

theorem IsPadicValIntPair_pairMul_add_lower_bound {p j k s : BHist} {x y : BHist × BHist} :
    IsPadicValIntPair p x j -> IsPadicValIntPair p y k -> NatAdd j k s ->
      PDvdIntPair p s (pairMul x y) := by
  intro left right add
  exact PDvdIntPair_pairMul_add
    (And.intro left.left (And.intro left.right.left.left left.right.right.left))
    (And.intro right.left (And.intro right.right.left.left right.right.right.left)) add

theorem IsPadicValIntPair_pairMul_add_exact_with_obstruction {p j k s : BHist}
    {x y : BHist × BHist} :
    IsPadicValIntPair p x j -> IsPadicValIntPair p y k -> NatAdd j k s ->
      PadicIntPairProductExactnessObstruction p s (pairMul x y) ->
        IsPadicValIntPair p (pairMul x y) s := by
  intro left right add obstruction
  have lower := IsPadicValIntPair_pairMul_add_lower_bound left right add
  exact And.intro lower.left
    (And.intro (And.intro lower.right.left obstruction.left)
      (And.intro lower.right.right obstruction.right))

end BEDC.Derived.PadicUp
