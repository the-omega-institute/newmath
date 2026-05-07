import BEDC.Derived.HolomorphicUp

namespace BEDC.Derived.HolomorphicUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem HolomorphicLedgerPolicy_extension_gap_no_zero_head
    {center radius point extra gap extendedGap tail : BHist} :
    HolomorphicOpenDiskWitnessed center radius point -> UnaryHistory extra ->
      Cont point gap radius -> Cont gap extra extendedGap ->
        hsame extendedGap (BHist.e0 tail) -> False := by
  intro disk extraUnary pointGap gapExtra sameZeroHead
  cases disk with
  | intro _centerUnary rest =>
      cases rest with
      | intro _radiusUnary rest =>
          cases rest with
          | intro _pointUnary gapWitness =>
              cases gapWitness with
              | intro witnessedGap witnessedData =>
                  have gapSame : hsame gap witnessedGap :=
                    cont_left_cancel pointGap witnessedData.right
                  have gapUnary : UnaryHistory gap :=
                    unary_transport witnessedData.left (hsame_symm gapSame)
                  have extendedGapUnary : UnaryHistory extendedGap :=
                    unary_cont_closed gapUnary extraUnary gapExtra
                  have zeroHeadUnary : UnaryHistory (BHist.e0 tail) :=
                    unary_transport extendedGapUnary sameZeroHead
                  exact unary_no_zero_extension zeroHeadUnary

end BEDC.Derived.HolomorphicUp
