import BEDC.Derived.EgorovUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EgorovUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem Egorov_regseqrat_dyadic_tolerance_nonescape [AskSetup] [PackageSetup]
    {M Omega F X S R A W U L H C P N toleranceRead dyadicRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EgorovCarrier M Omega F X S R A W U L H C P N bundle pkg ->
      Cont R W toleranceRead ->
        Cont toleranceRead U dyadicRead ->
          Cont dyadicRead L terminalRead ->
            PkgSig bundle P pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row W ∨ hsame row U ∨ hsame row L ∨
                      hsame row toleranceRead ∨ hsame row dyadicRead ∨
                        hsame row terminalRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont R W toleranceRead ∧
                      Cont toleranceRead U dyadicRead ∧ Cont dyadicRead L terminalRead ∧
                        PkgSig bundle P pkg)
                  hsame ∧
                UnaryHistory toleranceRead ∧ UnaryHistory dyadicRead ∧
                  UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory hsame SemanticNameCert
  intro carrier toleranceRoute dyadicRoute terminalRoute provenancePkg
  obtain ⟨_packetWitness, _measureUnary, _probUnary, _familyUnary, _limitUnary,
    _scheduleUnary, readbackUnary, _exceptionalUnary, windowUnary, uniformityUnary,
    ledgerUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _provenancePkgCarrier, _localNamePkg⟩ := carrier
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed readbackUnary windowUnary toleranceRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed toleranceUnary uniformityUnary dyadicRoute
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed dyadicUnary ledgerUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row U ∨ hsame row L ∨
              hsame row toleranceRead ∨ hsame row dyadicRead ∨ hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont R W toleranceRead ∧
              Cont toleranceRead U dyadicRead ∧ Cont dyadicRead L terminalRead ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead
        ⟨hsame_refl terminalRead, terminalUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, toleranceRoute, dyadicRoute, terminalRoute, provenancePkg⟩
  }
  exact ⟨cert, toleranceUnary, dyadicUnary, terminalUnary⟩

end BEDC.Derived.EgorovUp
