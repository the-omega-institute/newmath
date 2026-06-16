import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyRingUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RegularCauchyRingCarrier [AskSetup] [PackageSetup]
    (A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory A ∧ UnaryHistory B ∧ UnaryHistory WA ∧ UnaryHistory WB ∧
    UnaryHistory DA ∧ UnaryHistory DB ∧ UnaryHistory S ∧ UnaryHistory G ∧
      UnaryHistory M ∧ UnaryHistory L ∧ UnaryHistory RS ∧ UnaryHistory RG ∧
        UnaryHistory RM ∧ UnaryHistory RL ∧ UnaryHistory ES ∧ UnaryHistory EG ∧
          UnaryHistory EM ∧ UnaryHistory EL ∧ UnaryHistory H ∧ UnaryHistory C ∧
            UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧
              PkgSig bundle N pkg

theorem RegularCauchyRingCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg →
      PkgSig bundle P pkg →
        PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist =>
                RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL
                  H C P N bundle pkg ∧ hsame row N)
              (fun row : BHist =>
                hsame row A ∨ hsame row B ∨ hsame row WA ∨ hsame row WB ∨
                  hsame row DA ∨ hsame row DB ∨ hsame row S ∨ hsame row G ∨
                    hsame row M ∨ hsame row L ∨ hsame row RS ∨ hsame row RG ∨
                      hsame row RM ∨ hsame row RL ∨ hsame row ES ∨ hsame row EG ∨
                        hsame row EM ∨ hsame row EL ∨ hsame row H ∨ hsame row C ∨
                          hsame row P ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory S ∧ UnaryHistory G ∧ UnaryHistory M ∧ UnaryHistory L ∧
              PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame SemanticNameCert UnaryHistory PkgSig
  intro carrier provenancePkg namePkg
  obtain ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, sUnary, gUnary, mUnary,
    lUnary, rsUnary, rgUnary, rmUnary, rlUnary, esUnary, egUnary, emUnary, elUnary,
    hUnary, cUnary, pUnary, nUnary, _carrierProvenancePkg, _carrierNamePkg⟩ := carrier
  have carrierForSource :
      RegularCauchyRingCarrier A B WA WB DA DB S G M L RS RG RM RL ES EG EM EL H C P N
        bundle pkg :=
    ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, sUnary, gUnary, mUnary,
      lUnary, rsUnary, rgUnary, rmUnary, rlUnary, esUnary, egUnary, emUnary, elUnary,
      hUnary, cUnary, pUnary, nUnary, provenancePkg, namePkg⟩
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro N ⟨carrierForSource, hsame_refl N⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        right
        exact source.right
      ledger_sound := by
        intro _row source
        exact ⟨unary_transport nUnary (hsame_symm source.right), provenancePkg, namePkg⟩
    }
  · exact ⟨sUnary, gUnary, mUnary, lUnary, namePkg⟩

end BEDC.Derived.RegularCauchyRingUp
