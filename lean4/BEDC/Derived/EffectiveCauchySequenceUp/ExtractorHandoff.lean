import BEDC.Derived.EffectiveCauchySequenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EffectiveCauchySequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EffectiveCauchySequenceExtractorHandoff [AskSetup] [PackageSetup]
    {S M W D Q E H C P N modulusRead windowRead dyadicRead regRead realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SemanticNameCert
        (fun row : BHist =>
          exists S' M' W' D' Q' E' H' C' P' N' : BHist,
            EffectiveCauchySequenceUp.mk S M W D Q E H C P N =
                EffectiveCauchySequenceUp.mk S' M' W' D' Q' E' H' C' P' N' ∧
              hsame row N')
        (fun row : BHist =>
          exists S' M' W' D' Q' E' H' C' P' N' : BHist,
            EffectiveCauchySequenceUp.mk S M W D Q E H C P N =
                EffectiveCauchySequenceUp.mk S' M' W' D' Q' E' H' C' P' N' ∧
              hsame row N')
        (fun row : BHist =>
          exists S' M' W' D' Q' E' H' C' P' N' : BHist,
            EffectiveCauchySequenceUp.mk S M W D Q E H C P N =
                EffectiveCauchySequenceUp.mk S' M' W' D' Q' E' H' C' P' N' ∧
              hsame row N')
        hsame →
      UnaryHistory S →
        UnaryHistory M →
          UnaryHistory W →
            UnaryHistory D →
              UnaryHistory Q →
                UnaryHistory E →
                  Cont S M modulusRead →
                    Cont modulusRead W windowRead →
                      Cont windowRead D dyadicRead →
                        Cont dyadicRead Q regRead →
                          Cont regRead E realRead →
                            PkgSig bundle realRead pkg →
                              SemanticNameCert
                                (fun row : BHist => hsame row realRead ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row Q ∨
                                    hsame row E ∨ hsame row realRead)
                                (fun row : BHist =>
                                  UnaryHistory row ∧ Cont S M modulusRead ∧
                                    Cont modulusRead W windowRead ∧
                                      Cont windowRead D dyadicRead ∧
                                        Cont dyadicRead Q regRead ∧ Cont regRead E realRead ∧
                                          PkgSig bundle realRead pkg)
                                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory hsame SemanticNameCert
  intro obligations sourceUnary modulusUnary windowUnary dyadicUnary regUnary sealUnary
    modulusRoute windowRoute dyadicRoute regRoute realRoute realPkg
  have _localNameWitness :
      exists row : BHist,
        exists S' M' W' D' Q' E' H' C' P' N' : BHist,
          EffectiveCauchySequenceUp.mk S M W D Q E H C P N =
              EffectiveCauchySequenceUp.mk S' M' W' D' Q' E' H' C' P' N' ∧
            hsame row N' :=
    semanticNameCert_ledger_policy_witness obligations
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed sourceUnary modulusUnary modulusRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed modulusReadUnary windowUnary windowRoute
  have dyadicReadUnary : UnaryHistory dyadicRead :=
    unary_cont_closed windowReadUnary dyadicUnary dyadicRoute
  have regReadUnary : UnaryHistory regRead :=
    unary_cont_closed dyadicReadUnary regUnary regRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed regReadUnary sealUnary realRoute
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro realRead ⟨hsame_refl realRead, realReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modulusRoute, windowRoute, dyadicRoute, regRoute, realRoute,
          realPkg⟩
  }

end BEDC.Derived.EffectiveCauchySequenceUp
