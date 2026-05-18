import BEDC.Derived.AuthorizedGeneratorRecursorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.AuthorizedGeneratorRecursorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem AuthorizedGeneratorRecursor_root_output_audit_totality
    [AskSetup] [PackageSetup]
    {I E M B D O A _H _C P _G N branchRead descentRead outputRead auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory I ->
      UnaryHistory E ->
        UnaryHistory M ->
          UnaryHistory B ->
            UnaryHistory D ->
              UnaryHistory O ->
                UnaryHistory A ->
                  UnaryHistory N ->
                    Cont I E branchRead ->
                      Cont M D descentRead ->
                        Cont O A outputRead ->
                          Cont outputRead N auditRead ->
                            PkgSig bundle P pkg ->
                              SemanticNameCert
                                (fun row : BHist => hsame row N ∧ UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row N ∧ Cont I E branchRead ∧
                                    Cont M D descentRead ∧ Cont O A outputRead ∧
                                      Cont outputRead N auditRead)
                                (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                                hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro _unaryI _unaryE _unaryM _unaryB _unaryD _unaryO _unaryA unaryN branchRoute
    descentRoute outputRoute auditRoute pkgSig
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
      exact ⟨source.left, branchRoute, descentRoute, outputRoute, auditRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgSig⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
