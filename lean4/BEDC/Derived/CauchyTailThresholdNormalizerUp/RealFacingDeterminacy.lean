import BEDC.Derived.CauchyTailThresholdNormalizerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyTailThresholdNormalizerRealFacingDeterminacy [AskSetup] [PackageSetup]
    {S M Theta W0 W1 D R A E H C P L N sourceRead sealRead windowRead agreementRead
      realRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory M →
        UnaryHistory Theta →
          UnaryHistory W0 →
            UnaryHistory W1 →
              UnaryHistory D →
                UnaryHistory R →
                  UnaryHistory A →
                    Cont S M sourceRead →
                      Cont sourceRead Theta sealRead →
                        Cont sealRead W0 windowRead →
                          Cont windowRead W1 agreementRead →
                            Cont agreementRead A realRead →
                              PkgSig bundle P pkg →
                                SemanticNameCert
                                    (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row S ∨ hsame row M ∨ hsame row Theta ∨
                                        hsame row W0 ∨ hsame row W1 ∨ hsame row D ∨
                                          hsame row R ∨ hsame row A ∨ hsame row E ∨
                                            hsame row H ∨ hsame row C ∨ hsame row P ∨
                                              hsame row L ∨ hsame row N ∨ hsame row realRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont S M sourceRead ∧
                                        Cont sourceRead Theta sealRead ∧
                                          Cont sealRead W0 windowRead ∧
                                            Cont windowRead W1 agreementRead ∧
                                              Cont agreementRead A realRead ∧
                                                PkgSig bundle P pkg)
                                    hsame ∧
                                  UnaryHistory realRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sUnary mUnary thetaUnary w0Unary w1Unary _dUnary _rUnary aUnary sourceRoute
    sealRoute windowRoute agreementRoute realRoute provenancePkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sUnary mUnary sourceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceUnary thetaUnary sealRoute
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed sealUnary w0Unary windowRoute
  have agreementUnary : UnaryHistory agreementRead :=
    unary_cont_closed windowUnary w1Unary agreementRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed agreementUnary aUnary realRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Theta ∨ hsame row W0 ∨ hsame row W1 ∨
              hsame row D ∨ hsame row R ∨ hsame row A ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row L ∨ hsame row N ∨ hsame row realRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M sourceRead ∧ Cont sourceRead Theta sealRead ∧
              Cont sealRead W0 windowRead ∧ Cont windowRead W1 agreementRead ∧
                Cont agreementRead A realRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro realRead ⟨hsame_refl realRead, realUnary⟩
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, sealRoute, windowRoute, agreementRoute,
          realRoute, provenancePkg⟩
  }
  exact ⟨cert, realUnary⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
