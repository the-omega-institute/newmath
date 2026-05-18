import BEDC.Derived.ClosedSubstitutionBoundaryUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.ClosedSubstitutionBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedSubstitutionBoundaryNameCertObligations
    [AskSetup] [PackageSetup]
    {T D V K R Q H C P N substituteRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory T →
      UnaryHistory D →
        UnaryHistory V →
          UnaryHistory K →
            UnaryHistory R →
              UnaryHistory Q →
                UnaryHistory C →
                  UnaryHistory N →
                    Cont K Q substituteRead →
                      Cont substituteRead C publicRead →
                        hsame H BHist.Empty →
                          PkgSig bundle P pkg →
                            SemanticNameCert
                              (fun row : BHist => hsame row N ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row N ∧ UnaryHistory T ∧ UnaryHistory D ∧
                                  UnaryHistory V ∧ UnaryHistory K ∧ UnaryHistory R ∧
                                    UnaryHistory Q ∧ Cont K Q substituteRead ∧
                                      Cont substituteRead C publicRead ∧
                                        hsame H BHist.Empty)
                              (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                              hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro unaryT unaryD unaryV unaryK unaryR unaryQ _unaryC unaryN substituteRoute
    publicRoute emptyTransport pkgSig
  have sourceN : (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro N sourceN
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
        exact ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, unaryT, unaryD, unaryV, unaryK, unaryR, unaryQ, substituteRoute,
          publicRoute, emptyTransport⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgSig⟩
  }

end BEDC.Derived.ClosedSubstitutionBoundaryUp
