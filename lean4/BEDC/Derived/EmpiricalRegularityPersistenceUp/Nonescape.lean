import BEDC.Derived.EmpiricalRegularityPersistenceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.EmpiricalRegularityPersistenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EmpiricalRegularityPersistenceCarrier_nonescape [AskSetup] [PackageSetup]
    {M R K L G A S F H C P N lawRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EmpiricalRegularityPersistenceCarrier M R K L G A S F H C P N bundle pkg ->
      Cont A S lawRead ->
        PkgSig bundle lawRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row lawRead ∧ Cont A S lawRead)
              (fun row : BHist =>
                hsame row lawRead ∧ Cont M R K ∧ Cont K L G ∧ Cont G A S ∧
                  Cont A S lawRead)
              (fun row : BHist =>
                hsame row lawRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle lawRead pkg)
              hsame ∧
            UnaryHistory lawRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory SemanticNameCert hsame
  intro carrier lawRoute lawPackage
  obtain ⟨mUnary, rUnary, mrk, lUnary, klg, aUnary, gas, _fUnary, _sfh, _cUnary,
    pUnary, _nUnary, pPackage, _nPackage⟩ := carrier
  have kUnary : UnaryHistory K := unary_cont_closed mUnary rUnary mrk
  have gUnary : UnaryHistory G := unary_cont_closed kUnary lUnary klg
  have sUnary : UnaryHistory S := unary_cont_closed gUnary aUnary gas
  have lawUnary : UnaryHistory lawRead := unary_cont_closed aUnary sUnary lawRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact ⟨lawRead, hsame_refl lawRead, lawRoute⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _row' sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _row' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' sameRows source
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro row source
        exact ⟨source.left, mrk, klg, gas, source.right⟩
      ledger_sound := by
        intro row source
        exact ⟨source.left, pPackage, lawPackage⟩
    }
  · exact lawUnary

end BEDC.Derived.EmpiricalRegularityPersistenceUp
