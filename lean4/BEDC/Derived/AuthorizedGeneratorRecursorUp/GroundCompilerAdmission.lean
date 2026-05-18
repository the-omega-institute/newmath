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

theorem AuthorizedGeneratorRecursor_ground_compiler_admission
    [AskSetup] [PackageSetup]
    {U K O H P N authRead compilerRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory U ->
      UnaryHistory K ->
        UnaryHistory O ->
          UnaryHistory H ->
            UnaryHistory N ->
              Cont U K authRead ->
                Cont authRead O compilerRead ->
                  Cont compilerRead H publicRead ->
                    PkgSig bundle P pkg ->
                      SemanticNameCert
                        (fun row : BHist => hsame row N ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row N ∧ Cont U K authRead ∧ Cont authRead O compilerRead ∧
                            Cont compilerRead H publicRead)
                        (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro _unaryU _unaryK _unaryO _unaryH unaryN authRoute compilerRoute publicRoute pkgSig
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
      exact ⟨source.left, authRoute, compilerRoute, publicRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, pkgSig⟩
  }

end BEDC.Derived.AuthorizedGeneratorRecursorUp
