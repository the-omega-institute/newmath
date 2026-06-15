import BEDC.Derived.BinaryEndpointNormalizationUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BinaryEndpointNormalizationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BinaryEndpointNormalizationRealSealNonescape [AskSetup] [PackageSetup]
    {L R K D A W Q S H C P N sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory W →
      UnaryHistory D →
        UnaryHistory K →
          UnaryHistory A →
            UnaryHistory Q →
              UnaryHistory S →
                Cont W D K →
                  Cont K A Q →
                    Cont Q S sealRead →
                      PkgSig bundle sealRead pkg →
                        UnaryHistory sealRead ∧
                          SemanticNameCert
                            (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row K ∨ hsame row Q ∨ hsame row S ∨
                                hsame row sealRead)
                            (fun row : BHist =>
                              PkgSig bundle sealRead pkg ∧ hsame row sealRead)
                            hsame ∧
                            binaryEndpointNormalizationFromEventFlow
                                (binaryEndpointNormalizationToEventFlow
                                  (BinaryEndpointNormalizationUp.mk L R K D A W Q S H C P N)) =
                              some (BinaryEndpointNormalizationUp.mk L R K D A W Q S H C P N) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro windowUnary digitUnary _carryUnary approxUnary _handoffUnary sealUnary
    windowDigitCarry carryApproxHandoff handoffSealRead sealPkg
  have carryFromRoute : UnaryHistory K :=
    unary_cont_closed windowUnary digitUnary windowDigitCarry
  have handoffFromRoute : UnaryHistory Q :=
    unary_cont_closed carryFromRoute approxUnary carryApproxHandoff
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed handoffFromRoute sealUnary handoffSealRead
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row K ∨ hsame row Q ∨ hsame row S ∨ hsame row sealRead)
        (fun row : BHist => PkgSig bundle sealRead pkg ∧ hsame row sealRead)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact Or.inr (Or.inr (Or.inr source.left))
      ledger_sound := by
        intro _row source
        exact ⟨sealPkg, source.left⟩
    }
  have roundTrip :
      binaryEndpointNormalizationFromEventFlow
          (binaryEndpointNormalizationToEventFlow
            (BinaryEndpointNormalizationUp.mk L R K D A W Q S H C P N)) =
        some (BinaryEndpointNormalizationUp.mk L R K D A W Q S H C P N) :=
    BinaryEndpointNormalizationTasteGate_single_carrier_alignment.right.left
      (BinaryEndpointNormalizationUp.mk L R K D A W Q S H C P N)
  exact ⟨sealReadUnary, cert, roundTrip⟩

end BEDC.Derived.BinaryEndpointNormalizationUp
