import BEDC.Derived.PrefixObserverUp
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Sig
import BEDC.FKernel.Unary

namespace BEDC.Derived.PrefixObserverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Sig
open BEDC.FKernel.Unary

theorem PrefixObserverNameCertObligations
    [AskSetup] [PackageSetup]
    {S W R K U L _H _C Q N prefixRead consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S ->
      UnaryHistory W ->
        UnaryHistory R ->
          UnaryHistory K ->
            UnaryHistory U ->
              UnaryHistory L ->
                UnaryHistory N ->
                  Cont S R prefixRead ->
                    Cont U L consumerRead ->
                      PkgSig bundle Q pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row N ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row N ∧ Cont S R prefixRead ∧
                                Cont U L consumerRead)
                            (fun row : BHist => hsame row N ∧ PkgSig bundle Q pkg)
                            hsame ∧
                          UnaryHistory prefixRead ∧ UnaryHistory consumerRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame
  intro unaryS _unaryW unaryR _unaryK unaryU unaryL unaryN prefixRoute consumerRoute pkgSig
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed unaryS unaryR prefixRoute
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed unaryU unaryL consumerRoute
  have sourceN : (fun row : BHist => hsame row N ∧ UnaryHistory row) N := by
    exact ⟨hsame_refl N, unaryN⟩
  have semantic :
      SemanticNameCert
          (fun row : BHist => hsame row N ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row N ∧ Cont S R prefixRead ∧ Cont U L consumerRead)
          (fun row : BHist => hsame row N ∧ PkgSig bundle Q pkg)
          hsame := by
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
          exact
            ⟨hsame_trans (hsame_symm same) source.left, unary_transport source.right same⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, prefixRoute, consumerRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, pkgSig⟩
    }
  exact ⟨semantic, prefixUnary, consumerUnary⟩

end BEDC.Derived.PrefixObserverUp
